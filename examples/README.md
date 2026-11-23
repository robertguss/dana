# Dana Sample Programs (Phase 0 Syntax Corpus)

These 10 sample programs pressure-test Dana's syntax, structural table typing, privacy and
declassification rules, SQL pushdown, statistics, charting, and testing ergonomics before
freezing the v0.1 Language Reference and Dana Core IR.

Once the Phase 0 executable grammar (`grammar/`) and Phase 2 compiler exist, every file here
will parse, type-check, and pass its inline `examples` and `test` blocks in CI.

## Programs

| File | Domain | Features Exercised |
| --- | --- | --- |
| [expenses.dana](expenses.dana) | General CLI (sibling to Mo's `expenses.mo`) | Zero-friction public data, CSV quarantine `bad_rows`, `Decimal`, Markdown `table` literals, `Files.in_memory` |
| [enrollment-report.dana](enrollment-report.dana) | Higher Ed / FERPA Analytics | Postgres SQL pushdown, `[pii]`/`[ferpa]` taint, `suppress_small_groups(min: 5, distinct_by: .id)`, window functions, SVG charts, HTML `Report`, `DB.in_memory` |
| [registrar-sync.dana](registrar-sync.dana) | Higher Ed / API-to-DB ETL | Paginated `HttpsAllow` glue outside pure pipelines, quarantine parsing, `anti_join`, column-matched `WriteTable` upsert, `dana dry-run`, [dana.policy](dana.policy) |
| [research-export.dana](research-export.dana) | Institutional Research | Schema-level `[counseling]` tag, `Secret` + `pseudonymize`, Parquet & `.xlsx` export, authorized non-PII sink |
| [donor-reconciliation.dana](donor-reconciliation.dana) | Higher Ed / Finance | Custom `tag donor`, `.xlsx` read/write, exact `Decimal` conservation `promise`, `left_join_one` & `anti_join` |
| [course-outcomes-stats.dana](course-outcomes-stats.dana) | Exploratory Statistics | Public Parquet/CSV, `profile()`, `T?` missing values, `corr`, `linear_regression`, `t_test`, z-score outliers, SVG scatter chart |
| [saas-cohort-retention.dana](saas-cohort-retention.dana) | SaaS / Product Analytics | Monthly cohorts, MRR/churn, `pivot_wider` retention matrix, rolling window functions, SVG heatmap |
| [ecommerce-ledger-audit.dana](ecommerce-ledger-audit.dana) | Fintech / E-Commerce | Parquet + CSV + embedded SQLite, `join_many_to_one` duplicate-payout catch, double-entry `Decimal` promises |
| [log-anomaly-triage.dana](log-anomaly-triage.dana) | DevOps / SRE Logs | Streaming `.jsonl.gz`, `date_trunc` + `fill_gaps`, p50/p95/p99, z-score spikes, zero-false-alarm `[pii]` column isolation, `redact`, terminal + SVG charts |
| [hipaa-clinic-outcomes.dana](hipaa-clinic-outcomes.dana) | Healthcare / HIPAA | Built-in `[pii]` + `[health]` tags, `suppress_small_groups(min: 10, distinct_by: .patient_id)`, `dana.policy` ceiling |

## Policy Example

- [dana.policy](dana.policy): an opt-in human-readable upper-bound policy governing sensitive
  exports, HTTPS hosts, database table writes, and minimum group sizes.
