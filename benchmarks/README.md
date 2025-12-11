# Benchmarks

This folder contains all scripts necessary to reproduce the performance and correctness evaluation of BAss. The instructions
are presented as if the current working directory is the repository root.

## 0. Data preparation

If you downloaded this content from the github repository, make sure to first unzip the `./test_instances/_normalized.zip` file, 
since this file contains the additional BNs representations of the test instances in `.bnet` and `.sbml` format.

If you downloaded this content from the [Zenodo artefact](https://doi.org/10.5281/zenodo.17794231), this folder should be already
present. Furthemore, you can verify that `./benchmarks/results/raw` contains the full expected benchmark output across all tools
(due to their size, these files are not present in the github repository).

## 1. Running benchmarks

Make sure you have `docker` (or `podman`) and `python3` available on your machine (with `pandas` installed). All benchmarks 
then run in dedicated pre-built docker containers and should therefore require no additional setup or configuration.

There are two environment variables that can be used to modify the benchmark runs: `TIMEOUT` will be passed as an argument
to the native `timeout` utility to restrict runtime. Meanwhile, `PARALLEL` can be set to a number of benchmarks that can 
safely run at the same time. Default timeout is `10s`, default parallelism is one CPU core.

**Note that in the published configuration (timeout of `1200s`), each full tool benchmark can take 12+ hours even when running 
on 40-60 CPU cores. Outside of actual performance tests, we therfore recommend testing with a significantly smaller timeout. 
For example, with the default timeout and 4-8 CPU cores, most benchmark runs can be still completed in several hours. Do not
benchmark two tools at the same time (this can confuse the scripts gathering statistics)**

To reproduce the official results, use the following commands (or override `TIMEOUT` and `PARALLEL` with values that are suitable
in your scenario):

```bash
export TIMEOUT='1200s'
export PARALLEL='48'
./benchmarks/bench_adf-obdd.sh
./benchmarks/bench_aeon-py.sh
./benchmarks/bench_BAss.sh
./benchmarks/bench_bioLQM.sh
./benchmarks/bench_fASP.sh
./benchmarks/bench_goDiamond.sh
./benchmarks/bench_k++ADF.sh
./benchmarks/bench_mpbn.sh
./benchmarks/bench_tsconj.sh
./benchmarks/bench_yadf.sh
```

This should create a `./results` folder with various `run_*` directories identifying the problem and tool. Within the directory,
all output and statistics files should be present, plus a special `_result.csv` file with overall runtime statistics.

## 2. Benchmark analysis

The analysis of computed instances requires that corresponding `_result.csv` files are placed within `./benchmarks/results` into
problem-specific directories (the file itself should then be named after the tool that produced it; e.g. `__results.csv` file for
`BAss` solving problem `com` should be placed in `./benchmarks/results/com/bass.csv`). Results that were
used in the paper should already be present, so to test this step, you don't need your own full set of benchmark results. 

To perform the analysis of computed instances, run the following commands:

```bash
cd ./benchmarks/results

python3 process_results ./2v ./exclude.txt > 2v_stats.txt
mv summary.csv 2c_summary.csv

python3 process_results ./adm ./exclude.txt > adm_stats.txt
mv summary.csv adm_summary.csv

python3 process_results ./com ./exclude.txt > com_stats.txt
mv summary.csv com_summary.csv

python3 process_results ./prf ./exclude.txt > prf_stats.txt
mv summary.csv prf_summary.csv

python3 process_results ./stm ./exclude.txt > stm_stats.txt
mv summary.csv stm_summary.csv
```

If you are using the pre-computed result files, this should produce no change. Otherwise, the summary tables
and statistics files should now contain information reflecting your actual results.

The performance table in the paper is produced as from the individual `*_stats.txt` files.

Note that the `exclude.txt` file lists instances that could not be converted into
Boolean networks and are therefore excluded. You can remove these from the file
to obtain results which also count these instances. However, do note that some BN
tools do not correctly report these as errors, i.e. the numbers for BN tools may not
be accurate.

## 3. Running correctness check

To verify correcness, we first extract all benchmark instances that can be solved in under `10s` by all tested 
tools. To obtain these lists, you can run `python3 find_fast_instances.py`. Again, if you are using the provided
results, this should produce no change.

Afterwards, you can actually generate the tool outputs by running the following commands:

```bash
cd ./benchmarks

./record_adf-obdd.sh
./record_aeon-py.sh
./record_BAss.sh
./record_bioLQM.sh
./record_fASP.sh
./record_goDiamond.sh
./record_k++ADF.sh
./record_mpbn.sh
./record_tsconj.sh
./record_yadf.sh
```

Note that this process can still take several hours purely due to the high number of tools and benchmarks. At the end,
the resulting text files for each tool and problem combination should be placed in the `./benchmarks/results/recorded` folder.
These contain the full tool output. Expected results for this data are also already provided.

## 4. Checking correctness

Finally, to verify correctness, run the following commands:

```bash
cd ./benchmarks

python3 compare_results.py -p 2v
python3 compare_results.py -p stm
python3 compare_results.py -p com
python3 compare_results.py -p prf
python3 compare_results.py -p adm
```

This should list the compared tools and the number of test instances that were tested for correctness across these tools.
If any discrepancy is found, it will be reported.