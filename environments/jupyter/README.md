# Lean4 Jupyter Environment

Interactive Lean4 development environment using Jupyter notebooks with custom kernel support.

## Quick Start

```powershell
# Start the environment
podman-compose up -d

# Open browser to:
# http://localhost:8888
```

## Features

- 🚀 **Interactive Development**: Real-time Lean4 code execution
- 📚 **Built-in Tutorial**: Comprehensive Lean4 learning notebook
- 🔍 **Type Checking**: Immediate feedback on proofs and definitions
- 🎯 **Mathematical Libraries**: Full Mathlib integration
- 🌐 **Web Interface**: No local IDE required

## Tutorial Contents

The included `Lean4_Tutorial.ipynb` covers:

1. **Basic Syntax**: Commands and evaluation
2. **Functions & Types**: Definitions and type system
3. **Theorem Proving**: Basic proof techniques
4. **Mathematical Structures**: Working with Mathlib
5. **Advanced Techniques**: Induction, tactics, and more

## Kernel Features

The custom Lean4 kernel supports:

- **Code Execution**: Run Lean4 code directly in cells
- **Type Information**: Display types and proof states
- **Error Reporting**: Clear error messages with locations
- **Import Support**: Access to full Lean4 ecosystem

## Creating New Notebooks

1. Click "New" → "Lean4" in Jupyter Lab
2. Start with basic imports:
   ```lean4
   import Mathlib.Data.Nat.Basic
   import Mathlib.Tactic
   ```
3. Write and execute Lean4 code in cells

## Useful Commands

### In Lean4 cells:
```lean4
#check Nat                    -- Check type information
#eval 2 + 3                   -- Evaluate expressions  
#print List.length            -- Print definitions
```

### Example proof:
```lean4
theorem add_zero (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]
```

## Container Management

```powershell
# Start environment
podman-compose up -d

# Stop environment
podman-compose down

# View logs
podman-compose logs

# Rebuild container
podman-compose up --build
```

## Troubleshooting

**Kernel not starting**: Check container logs with `podman-compose logs`

**Port conflicts**: Change port in `docker-compose.yml` from 8888 to another port

**Memory issues**: Increase container memory limits in `docker-compose.yml`

## Next Steps

- Work through the tutorial notebook
- Explore [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- Try the [Natural Number Game](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
- Browse [Mathlib examples](https://leanprover-community.github.io/mathlib4_docs/)