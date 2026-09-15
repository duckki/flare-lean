# Source provenance

FLARE's initial theorem collection was derived from `formal-demo` at revision
`af1dd951770ee7d5b222331c31e0f3e885005681`. FLARE is an independent Lake package;
building it requires no source-project checkout.

The [source manifest](extraction-manifest.json) is the durable record of that
origin. It contains the source revision and toolchain, source-file SHA-256
hashes, destination paths, and notes identifying the portions reused. Repeated
destination paths mean that a module combines material from multiple source
files. The hashes describe the original source files, not current FLARE files.

The initial adaptation qualified namespaces, separated pure mathematics from
native reasoning, and replaced application error types with numerical errors.
It preserved theorem assumptions and native arithmetic schedules. The
manifest records the details without requiring an application history in the
library's API documentation.

Preserve these origin records when the library evolves, update destination
paths if modules move, and add source records when importing further results.
This document records origin; it does not establish mathematical novelty or
upstream acceptance. See the [theorem guide](reference.md) for current contracts.
