prague_start = start_days["Prague"]
prague_duration = cities["Prague"]
prague_end = prague_start + prague_duration - 1
if not (10 <= prague_start <= 12 and 10 <= prague_end <= 12):
    continue