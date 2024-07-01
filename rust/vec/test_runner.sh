#!/bin/bash
cargo test -p vec $1 --lib -- --nocapture --test-threads=1