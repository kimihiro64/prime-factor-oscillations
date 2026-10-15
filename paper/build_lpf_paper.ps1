param(
    [string]$PdfLatex = ''
)

$ErrorActionPreference = 'Stop'
$root = (Get-Item -LiteralPath (Join-Path $PSScriptRoot '..')).FullName
if ([string]::IsNullOrWhiteSpace($PdfLatex)) {
    $candidates = @(Get-Command pdflatex -CommandType Application -ErrorAction Stop |
        ForEach-Object { $_.Source } | Sort-Object -Unique)
    if ($candidates.Count -eq 0) { throw 'pdflatex was not found' }
    $PdfLatex = $candidates[0]
}
$PdfLatex = [IO.Path]::GetFullPath($PdfLatex)
if (-not (Test-Path -LiteralPath $PdfLatex -PathType Leaf)) {
    throw "Missing LaTeX executable: $PdfLatex"
}

$source = Join-Path $PSScriptRoot 'lpf-dynamics.tex'
$build = Join-Path $root '.research/audits/lpf-paper/tex'
[IO.Directory]::CreateDirectory($build) | Out-Null
& $PdfLatex --version *> (Join-Path $build 'compiler-version.txt')
if ($LASTEXITCODE -ne 0) { throw 'LaTeX version check failed' }
foreach ($pass in 1..3) {
    & $PdfLatex --disable-installer -interaction=nonstopmode -halt-on-error `
        -file-line-error "-output-directory=$build" $source `
        *> (Join-Path $build "pass$pass.txt")
    if ($LASTEXITCODE -ne 0) {
        throw "LaTeX pass $pass failed; inspect $build/pass$pass.txt"
    }
}
$log = Join-Path $build 'lpf-dynamics.log'
$failures = @(Select-String -LiteralPath $log -SimpleMatch -Pattern `
    'Overfull', 'undefined', 'Label(s) may have changed')
if ($failures.Count -gt 0) {
    throw "PDF layout/reference check failed; inspect $log"
}
Copy-Item -LiteralPath (Join-Path $build 'lpf-dynamics.pdf') `
    -Destination (Join-Path $PSScriptRoot 'lpf-dynamics.pdf')
$publicLog = Join-Path $PSScriptRoot 'verification/lpf-paper-build.log'
$lines = [IO.File]::ReadAllLines($log) | ForEach-Object { $_.TrimEnd() }
$text = (($lines -join [Environment]::NewLine).TrimEnd()) + [Environment]::NewLine
[IO.File]::WriteAllText($publicLog, $text, [Text.UTF8Encoding]::new($false))
Write-Output 'LPF paper built; no overfull boxes or unresolved references.'
