# check_book.ps1 - compiles every Lean example of the book with your project's Lean 4.35.0 and Mathlib,
# and checks that each block behaves as the book shows:
#   * it compiles without errors, or fails with the error the book quotes;
#   * each result the book prints in a comment after #eval, #check, #print or #synth is what Lean prints.
# Usage: double-click run_check.bat, or from the project folder:
#   powershell -ExecutionPolicy Bypass -File Book_Examples\check_book.ps1 [-Only Ch07]
param([string]$Only = "")
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$OutputEncoding = [System.Text.Encoding]::UTF8
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$root = Split-Path -Parent $here
if (-not ((Test-Path (Join-Path $root "lakefile.toml")) -or (Test-Path (Join-Path $root "lakefile.lean")))) {
    Write-Host "Put the Book_Examples folder inside your Lean project folder (the folder that contains lakefile.toml), then run this again." -ForegroundColor Red
    exit 1
}
if (-not (Get-Command lake -ErrorAction SilentlyContinue)) {
    Write-Host "The command 'lake' was not found. Run this from VS Code's terminal, or check your Lean installation (elan)." -ForegroundColor Red
    exit 1
}
$meta = Get-Content -Raw -Encoding UTF8 (Join-Path $here "expected.json") | ConvertFrom-Json
# the [leanOptions] of the book's lakefile.toml (lake env lean does not read them, so they are passed here)
$opts = @("--json", "-D", "pp.unicode.fun=true", "-D", "relaxedAutoImplicit=false", "-D", "maxSynthPendingDepth=3", "-D", "weak.linter.mathlibStandardSet=true")
$word = '^[A-Za-z0-9_.\u00C0-\u024F\u0370-\u03FF]$'

function Norm([string]$t) { (($t -replace '[`''"\u2018\u2019]', '') -replace '\s+', ' ').Trim().ToLowerInvariant() }
function IsWord($c) { return ([string]$c) -match $word }

# Every piece of the book's error text (cut at '…' and before '⊢') appears in Lean's text, in order.
function Test-BookMessage([string]$expected, [string]$actual) {
    $a = Norm $actual; $pos = 0; $whole = Norm $expected
    foreach ($frag in ($expected -split '…|\.\.\.|(?=⊢)')) {
        $f = Norm $frag
        if ($f.Length -lt 4 -and -not ($f -ne "" -and $f -eq $whole)) { continue }
        $k = $a.IndexOf($f, $pos, [StringComparison]::Ordinal)
        if ($k -lt 0) { return $false }
        $pos = $k + $f.Length
    }
    return $true
}

# The result in the book's comment is Lean's output, or a whole part of it (for #check, often the statement only).
function Test-BookResult([string]$expected, [string]$actual) {
    $a = Norm $actual; $pos = 0
    foreach ($frag in ($expected -split '…|\.\.\.')) {
        $f = Norm $frag
        if ($f -eq "") { continue }
        $k = $a.IndexOf($f, $pos, [StringComparison]::Ordinal)
        while ($k -ge 0) {
            $e = $k + $f.Length
            $okL = ($k -eq 0) -or -not (IsWord ($a[$k - 1])) -or -not (IsWord ($f[0]))
            $okR = ($e -eq $a.Length) -or -not (IsWord ($a[$e])) -or -not (IsWord ($f[$f.Length - 1]))
            if ($okL -and $okR) { break }
            $k = $a.IndexOf($f, $k + 1, [StringComparison]::Ordinal)
        }
        if ($k -lt 0) { return $false }
        $pos = $k + $f.Length
    }
    return $true
}

# Lean's messages, one JSON object per line. Other lines that report a crash count as errors on line 0.
function Get-LeanMessages([string[]]$lines) {
    $msgs = New-Object System.Collections.Generic.List[object]
    foreach ($l in $lines) {
        if ($l.Trim() -eq "") { continue }
        $m = $null
        if ($l.TrimStart().StartsWith("{")) { try { $m = $l | ConvertFrom-Json -ErrorAction Stop } catch { $m = $null } }
        if ($m -and $m.severity) {
            if ($m.isSilent) { continue }
            $kind = if ($m.severity -eq "information") { "info" } else { [string]$m.severity }
            $line = if ($m.pos) { [int]$m.pos.line } else { 0 }
            $msgs.Add([pscustomobject]@{ Line = $line; Kind = $kind; Text = [string]$m.data })
        } elseif ($l -match '(?i)error|panic|uncaught|stack overflow') {
            $msgs.Add([pscustomobject]@{ Line = 0; Kind = "error"; Text = $l })
        }
    }
    return ,$msgs
}
function First-Line([string]$t) { return (($t -split "`n") | Select-Object -First 1) }
function Short([string]$t, [int]$n) { $t = ($t -replace "`r?`n", " / "); if ($t.Length -gt $n) { $t.Substring(0, $n) + "..." } else { $t } }

$files = @($meta.files | Where-Object { $_.name -like "$Only*" })
if ($files.Count -eq 0) { Write-Host "No file matches '$Only'. Use a prefix such as Ch07." -ForegroundColor Red; exit 1 }
$report = New-Object System.Collections.Generic.List[string]
$report.Add("Compile check of the book's Lean examples - " + (Get-Date -Format "yyyy-MM-dd HH:mm"))
Push-Location $root
$lv = (& lake env lean --version 2>&1 | Out-String).Trim()
$report.Add("Lean: $lv")
if ($lv -notmatch '4\.35\.0') { $report.Add("Note: the book uses Lean 4.35.0. Results with another version can differ."); Write-Host "Note: this project does not use Lean 4.35.0 ($lv)." -ForegroundColor Yellow }
$report.Add("")
$total = 0; $good = 0; $nres = 0; $ndiff = 0; $n = 0; $mathlibChecked = $false
$start = Get-Date
foreach ($f in $files) {
    $n++
    Write-Host ("[{0}/{1}] {2}  ({3})" -f $n, $files.Count, $f.name, $f.chapter)
    $path = Join-Path (Join-Path $here "files") $f.name
    $old = $ErrorActionPreference; $ErrorActionPreference = "Continue"
    $raw = @(& lake env lean @opts $path 2>&1 | ForEach-Object { "$_" })
    $ErrorActionPreference = $old
    Set-Content -Path ($path + ".out") -Value $raw -Encoding UTF8
    $msgs = Get-LeanMessages $raw
    if (-not $f.plain -and -not $mathlibChecked) {
        $bad = @($msgs | Where-Object { $_.Kind -eq "error" -and $_.Line -le 1 -and $_.Text -match 'unknown module prefix|does not exist|object file|failed to read|could not find' })
        if ($bad.Count -gt 0) {
            Pop-Location
            Write-Host ""
            Write-Host "Lean could not load Mathlib in this project:" -ForegroundColor Red
            Write-Host (First-Line $bad[0].Text)
            Write-Host "In the project folder, run   lake exe cache get   then try again." -ForegroundColor Red
            exit 1
        }
        $mathlibChecked = $true
    }
    $lines = New-Object System.Collections.Generic.List[string]
    foreach ($b in $f.blocks) {
        if (-not $b.judge) { continue }
        $total++
        $where = "{0}, block {1} (page {2}, French page {3}, {4}, lines {5}-{6})" -f $f.name, $b.block, $b.page, $b.page_fr, $b.section, $b.first_line, $b.last_line
        $errs = @($msgs | Where-Object { $_.Kind -eq "error" -and $_.Line -ge $b.first_line -and $_.Line -le $b.last_line })
        if ($b.lint) { $errs = @($errs | Where-Object { -not $_.Text.StartsWith("-- Found") }) }
        $why = ""
        if ($b.kind -eq "exercise") {
            if ($errs.Count -gt 0) { $lines.Add(("NOTE  {0}: {1} error(s) until the exercise is solved, first: {2}" -f $where, $errs.Count, (First-Line $errs[0].Text))) }
        } elseif (@($b.required).Count -gt 0) {
            $text = ($errs | ForEach-Object { $_.Text }) -join "`n"
            if ($errs.Count -eq 0) { $why = "the book shows an error here, but Lean reported none" }
            else { foreach ($e in $b.required) { if (-not (Test-BookMessage $e $text)) { $why = "Lean's error differs from the book. Book: $e" } } }
        } else {
            foreach ($e in $errs) {
                $ok = $false
                foreach ($x in @($b.allowed)) { if (Test-BookMessage $x $e.Text) { $ok = $true } }
                if (-not $ok) { $why = "unexpected error at line {0}: {1}" -f $e.Line, (First-Line $e.Text); break }
            }
        }
        if ($why -eq "") { $good++ }
        else {
            $lines.Add("FAIL  ${where}: $why")
            foreach ($e in $errs) { $lines.Add(("      Lean says (line {0}): {1}" -f $e.Line, (Short $e.Text 400))) }
        }
        foreach ($o in @($b.outputs)) {
            $nres++
            $ln = [int]$o.line; $exp = [string]$o.text
            $got = (@($msgs | Where-Object { $_.Kind -eq "info" -and $_.Line -eq $ln }) | ForEach-Object { $_.Text }) -join "`n"
            if (-not (Test-BookResult $exp $got)) {
                $ndiff++
                if ($got -eq "") { $got = "(nothing)" }
                $lines.Add(("DIFF  {0}, line {1} (page {2}, French page {3}): the book shows   {4}   Lean prints   {5}" -f $f.name, $ln, $b.page, $b.page_fr, $exp, (Short $got 300)))
            }
        }
    }
    foreach ($e in $msgs) {
        if ($e.Kind -ne "error") { continue }
        $owner = @($f.blocks | Where-Object { $e.Line -ge $_.first_line -and $e.Line -le $_.last_line })
        if ($owner.Count -eq 0) { $total++; $lines.Add(("FAIL  {0}, line {1}: error outside the blocks: {2}" -f $f.name, $e.Line, (Short $e.Text 300))) }
        elseif (-not $owner[0].judge) { $total++; $lines.Add(("FAIL  {0}, line {1}: error in block {2}, repeated here as context: {3}" -f $f.name, $e.Line, $owner[0].block, (Short $e.Text 300))) }
    }
    $judged = @($f.blocks | Where-Object { $_.judge }).Count
    if (@($lines | Where-Object { $_.StartsWith("FAIL") -or $_.StartsWith("DIFF") }).Count -eq 0) { $report.Add(("OK    {0}: {1} blocks as in the book" -f $f.name, $judged)) }
    foreach ($l in $lines) { $report.Add($l) }
}
Pop-Location
$mins = [math]::Round(((Get-Date) - $start).TotalMinutes, 1)
$report.Add("")
$report.Add("Not compiled:")
foreach ($x in $meta.not_compiled) { $report.Add(("      page {0} (French page {1}), {2}: {3}" -f $x.page, $x.page_fr, $x.chapter, $x.reason)) }
$summary = "RESULT: $good of $total blocks compile as the book shows. $($nres - $ndiff) of $nres results printed in comments match Lean's output. ($mins minutes)"
$report.Add(""); $report.Add($summary)
$report | Set-Content -Path (Join-Path $here "report.txt") -Encoding UTF8
Write-Host ""
if ($good -eq $total -and $ndiff -eq 0) { Write-Host $summary -ForegroundColor Green } else { Write-Host $summary -ForegroundColor Yellow }
Write-Host "Details: Book_Examples\report.txt"
