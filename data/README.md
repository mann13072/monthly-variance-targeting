# Data

The raw data are **not** redistributed here.

## Ken French daily three-factor files (needed to rerun the frozen test)
Download from the Kenneth R. French Data Library (Dartmouth): "Europe", "Japan" and "Asia Pacific ex Japan" daily 3-factor files, and "Fama/French 3 Factors [Daily]" for the US development file. The files used were created from the 202609 Bloomberg database and accessed 22 November 2026. Save them as:

    raw/data/french/regions/Europe_3_Factors_Daily.csv
    raw/data/french/regions/Japan_3_Factors_Daily.csv
    raw/data/french/regions/Asia_Pacific_ex_Japan_3_Factors_Daily.csv
    raw/data/french/F-F_Research_Data_Factors_daily.csv

SHA-256 of the files used (from results/freeze_practical_2026-11-22.txt); your download must match to reproduce the numbers exactly:

    9d76d27f486206667a6bcdf18dde487b11505ba637e8159f23810ecdf3e265b7  Europe_3_Factors_Daily.csv
    76af572edb587bb42f4fa43f276c499510a23e26895042cd366508e264ad81ab  Japan_3_Factors_Daily.csv
    ad87e5517e05cfea36e0ef95631ba74e2b82ce4dcfbdc88ca811533228f3b680  Asia_Pacific_ex_Japan_3_Factors_Daily.csv

(The French library may later revise these files; a different hash means different data.)

## ETF price files (not reproducible by outsiders)
The fund-shortfall and USD 100,000 account results (etf_shortfall_sso_spy.py, xs2d_shortfall.py, account_sim_100k.py) used unofficial public price series (SSO, SPY, S&P 500 total return index, XS2D.L) saved on 2026-11-22. They are not redistributed. Their result files are included for inspection only; those scripts cannot be rerun without your own copy of such data, and the paper labels this material development evidence.
