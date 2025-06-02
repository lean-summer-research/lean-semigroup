# Project Structure

## Files and Organization

### Main Project Files (`MyProject` folder)
- **PnatPow.lean**: Defines exponentiation for semigroups using positive natural numbers
- **WithOne.lean**: Implements the `S¹` construction for turning semigroups into monoids
- **Idempotence.lean**: Proves theorems about idempotent elements in finite semigroups

#### `MyProject/GreensRelations` folder
- **Defs.lean**: Formalizes Green's relations (R, L, J, H, and D). This file contains Definitions and alternative definitions based on Ideals, anlong with other characterizatoins of Greens Relations
- **Quot.lean**: This file deals with the representation of equivilance classes of Greens Equivalences as a `Quot` type.
- **Decidable.lean**: This contains things related to Decidability and Fintype instances for working with Greens relations on concrete examples of Semigroups.
- **Basic.lean**: This contains lemmas that build upon the foundation defined in earlier files.

### Examples (`Examples` folder)
- **Threemap.lean**: Defines the monoid of functions on {0,1,2} under composition and characterizes Greens relations on it. Demonstrates stuff from `MyProject.GreensRelations.Decidable.lean`
- **HSversion.lean**: Unchanged
- **GreensRelationsHS.lean**: Unchanged

## Import Structure
```
Mathlib
  ↓
PnatPow.lean
  ↓
WithOne.lean
  ↓
Idempotence.lean
  ↓
GreensRelations.Defs.lean
  ↓
GreensRelations.Quot.lean
  ↓
GreensRelations.Decidable.lean
  ↓
GreensRelations.Basic.lean
```

# Using Github Codespaces

There are two ways to use this repository:

1. Clone the repository and use it normally, ignoring the `.devcontainer` folder.
2. (also easy) Use GitHub Codespaces, which gives you a pre-configured development environment in your browser (explained below).

When you open this repo in a codespace, you'll see a VS Code interface in your browser. It's automatically set up with the LEAN4 vscode extention, correct lean version, and mathlib cache. It all runs on github's infra, so you don't have to worry about any of your local Lean, Elan, or VScode installations.

## First Time Setup:
1. Click the green "<> Code" button at the top of this GitHub page
2. Select "Codespaces" tab
3. Click "Create codespace"
4. Wait about 5-10 minutes for initial setup

## Basic Git Commands:
  First you have to open the integrated terminal (Mac: `Cmd+(backtick)`, Windows: `Ctrl+(backtick)`)

```bash
# Download latest changes
git pull

# Save your changes
# Stage all changes in the current working directory (make sure you are in the directory you want to save)
git add .

# Save changes locally
git commit -m "example"

# Upload changes to GitHub
git push
```

## Returning Later:
Go back to the repository's "<> Code" button, select "Codespaces" tab, and click your existing codespace (starts a lot faster than the initial build).

## How It Works (and how to do it locally)

The `.devcontainer` folder contains configuration files for a "dev container," which is like a small virtual machine. It sets up everything needed, like the operating system and software such as VSCode and Lean. GitHub Codespaces uses these files to create a development environment in the cloud, using Docker to manage the setup.

Docker is a tool that runs dev containers on your local computer. If you prefer not to use GitHub's cloud, you can run the same dev container locally instead of using Codespaces:

1. Install Docker Desktop from docker.com
2. In VS Code, install the "Dev Containers" extension
3. Clone this repository
4. Open the folder in VS Code
5. Click "Reopen in Container" when prompted

This will give you the same environment as Codespaces but running on your local machine. The VScode extension should automatically reopen the same container when you reopen the folder so you only have to build the container once.
