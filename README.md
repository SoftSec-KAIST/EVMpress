# EVMpress

A tool that analyzes function Control-Flow Graphs (CFGs) and type information
from an EVM bytecode.

+ EVMpress: Precise Type Inference for Next-Generation EVM Decompilation:
  [(link)]()

To reproduce our work, please refer to [this document](https://github.com/SoftSec-KAIST/EVMpress-artifact.git).

We implement CFG recovery in [B2R2](https://github.com/B2R2-org/B2R2.git), a
binary analysis framework, and use it as a building block for EVMpress.

## Requirements

+ Dotnet 9+

## How to use

You can run EVMpress using the following command:

```bash
dotnet run {{hex_path}} {{out_path}}
```

where `{{hex_path}}` is the path to the input EVM bytecode file and
`{{out_path}}` is the path to the output file.
Note that the input file must be in hexadecimal format, not binary.

### Graphical User Interface (GUI)

Leveraging the power of B2R2, a user-friendly GUI is provided, allowing users to
easily analyze EVM bytecode without needing to use the command line. It is
especially useful for users who want to analyze CFGs visually.

You can run `B2R2.RearEnd.BinExplorer` [(link)](https://github.com/B2R2-org/B2R2/tree/main/src/RearEnd/BinExplorer)
to launch the GUI. For example, ```dotnet run {{hex_path}} -A EVM```.
