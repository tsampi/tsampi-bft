# Public source policy

Every tracked file must be self-contained or refer only to publicly accessible
sources and dependencies. Documentation, source, tests and build targets must
work from this repository after installing the documented public toolchains.
Keep local Git metadata and generated build files out of commits.

If an inaccessible reference or dependency is introduced, remove it and squash
the correction into the affected commit. Rewrite and force-push the corrected
history when that commit has already been pushed.
