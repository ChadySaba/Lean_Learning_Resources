@echo off
rem Double-click to check every example of the book. Put the Book_Examples folder inside your Lean project folder first.
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0check_book.ps1" %*
pause
