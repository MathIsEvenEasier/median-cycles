Running the public Lean verification
===================================

The public workflow uses a single-use self-hosted Azure runner. It never
executes project proofs on the maintainer's computer. Provisioning is
separate from dispatch so the VM already has a deletion deadline before
GitHub starts executing project code.

Prerequisites: an authenticated Azure CLI, an enabled Free Trial or
Pay-As-You-Go subscription, an authenticated GitHub CLI with repository
runner-management and workflow rights, Python 3, and the required Azure
resource providers. Set AZURE_SUBSCRIPTION_ID to the chosen subscription.
GH_BIN optionally selects the GitHub CLI executable.

1. Run ``python3 ci/azure/audit.py prepare``. This writes a private job
   directory under ci/azure/runs and obtains a short-lived runner token.
2. Run ``python3 ci/azure/audit.py launch JOB_DIRECTORY``. Preflight checks
   the quota, VM image, and current compute price. The controller arms an
   independent one-shot Logic App before provisioning the worker.
3. Dispatch lean.yml on main with runner_label ``azure-proof-JOB_ID``.
   GitHub's workflow is the public record of the exact source commit.
4. Wait for the workflow conclusion, download its verification artifact,
   then run ``python3 ci/azure/audit.py collect JOB_DIRECTORY``. Collection
   preserves successful and failed diagnostics and deletes the resources.
5. Run ``python3 ci/azure/audit.py status JOB_DIRECTORY`` and verify
   all_deleted=true. Preserve a sanitized cleanup receipt with the build
   evidence. Never commit the private job directory or signed storage URLs.

Limits: four vCPUs, 24 GiB cgroup memory, no swap, 115 minutes for the whole
worker, 110 minutes for the workflow, 180 seconds per project module.
The independent guard requests deletion of compute resources 125 minutes
after cloud setup begins, even if the controller computer disconnects.
Recovery storage is retained until outputs are collected. A deadline is
a deletion request, not an exact billing cap. No inbound networking is
allowed. The preflight refuses VM compute prices over USD 0.25/hour;
disk, storage, network, and Logic App charges are additional.

A successful runner process is not a successful proof. Require the public
workflow conclusion, every positive module, the expected rejected negative
control, the final declaration audit, matching source hashes, and the
cleanup receipt. The pinned mathlib dependency cache is trusted as part
of the Lean build environment; this is not an independent-kernel audit.
