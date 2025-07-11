# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

CommunityModules is a community-driven repository of reusable TLA+ modules and operators that extend the standard TLA+ library. It provides additional operators for data structures, I/O operations, visualization, mathematics, and distributed systems concepts.

## Essential Commands

### Build Commands
```bash
# Initialize build directories
ant init

# Download TLA+ tools (tla2tools.jar v1.8.0)
ant download

# Compile Java module overrides
ant compile

# Create distribution JARs
ant dist

# Run all tests
ant test

# Clean build artifacts
ant clean
```

### Test Commands
```bash
# Run all module tests via TLC
ant test

# Run specific test module (example)
java -XX:+UseParallelGC -cp tlc/tla2tools.jar:dist/CommunityModules.jar tlc2.TLC tests/SequencesExtTests.tla
```

## Architecture

### Module Structure
- **TLA+ Modules** (`modules/*.tla`): Pure TLA+ specifications defining operators
- **Java Overrides** (`modules/tlc2/overrides/*.java`): Performance-optimized Java implementations for TLC
- **Test Modules** (`tests/*Tests.tla`): Test specifications that verify module behavior
- **Central Test Runner** (`tests/AllTests.tla`): Extends all individual test modules

### Key Design Patterns
1. **Module Overrides**: Many TLA+ operators have corresponding Java implementations for better TLC performance
2. **Dual Distribution**: 
   - `CommunityModules.jar`: Basic module package
   - `CommunityModules-deps.jar`: Includes all external dependencies
3. **Test Architecture**: Each module has a corresponding test module with ASSUME statements for verification

### Module Categories
- **Data Structures**: BagsExt, FiniteSetsExt, SequencesExt, Functions
- **I/O & Serialization**: IOUtils, CSV, Json
- **Visualization**: GraphViz, SVG, ShiViz, HTML
- **Mathematics**: Combinatorics, Statistics, DyadicRationals, Bitwise
- **Graph Theory**: Graphs, UndirectedGraphs
- **Distributed Systems**: VectorClocks
- **Advanced Operations**: Folds, Relation, DifferentialEquations

## Development Guidelines

### Adding New Modules
1. Create TLA+ module in `modules/` directory
2. Optionally add Java override in `modules/tlc2/overrides/`
3. Create corresponding test module in `tests/`
4. Add test module to EXTENDS list in `tests/AllTests.tla`
5. Update README.md with module description

### Java Override Conventions
- Package: `tlc2.overrides` 
- Class name must match TLA+ module name
- Implement methods matching TLA+ operator names
- Use `@TLAPrimitive` annotation for operator methods
- Target Java 8 compatibility

### Testing Best Practices
- Use ASSUME statements for test assertions
- Test both positive and negative cases
- Include edge cases and boundary conditions
- Verify Java overrides match TLA+ semantics

## CI/CD Pipeline

GitHub Actions workflow (`main.yml`):
1. Triggers on push (excluding README changes)
2. Builds project with `ant dist`
3. Creates timestamped release
4. Uploads JAR artifacts to GitHub release
5. Triggers downstream build in tlaplus/tlaplus repository

## External Dependencies

Located in `lib/` directory:
- Apache Commons (Lang3, Math3) - Utility functions
- Google Gson - JSON processing
- JGraphT - Graph algorithms
- SLF4J - Logging framework
- JUnit & Hamcrest - Testing (for Java tests only)