param(
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]] $LakeArguments = @('build')
)

$ErrorActionPreference = 'Stop'
$taskProject = $PSScriptRoot
$taskToolchain = (Get-Content -LiteralPath (Join-Path $taskProject 'lean-toolchain') -Raw).Trim()
$taskDirectoryName = $taskToolchain.Replace('/', '--').Replace(':', '---')
$taskRoots = @($env:ELAN_HOME, (Join-Path $env:USERPROFILE '.elan')) | Where-Object { $_ }
$taskLake = $null
foreach ($taskRoot in $taskRoots) {
    $taskCandidate = Join-Path $taskRoot "toolchains/$taskDirectoryName/bin/lake.exe"
    if (Test-Path -LiteralPath $taskCandidate) {
        $taskLake = $taskCandidate
        break
    }
}
if (-not $taskLake) {
    $taskLakeCommand = Get-Command lake -ErrorAction SilentlyContinue
    if (-not $taskLakeCommand) {
        throw "Lake was not found. Install the toolchain specified by lean-toolchain."
    }
    $taskLake = $taskLakeCommand.Source
}
$taskPreviousPath = $env:PATH
try {
    $env:PATH = (Split-Path -Parent $taskLake) + [IO.Path]::PathSeparator + $env:PATH
    Push-Location -LiteralPath $taskProject
    try {
        & $taskLake @LakeArguments
        if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    } finally { Pop-Location }
} finally { $env:PATH = $taskPreviousPath }
