# Example list of possible start dates for Prague
possible_start_dates = [10, 11, 12, 13, 14]

# Duration of the trip in Prague
prague_duration = cities["Prague"]

for prague_start in possible_start_dates:
    prague_end = prague_start + prague_duration - 1
    if not (10 <= prague_start <= 12 and 10 <= prague_end <= 12):
        continue
    # Proceed with valid date range
    print(f"Valid dates for Prague: Start={prague_start}, End={prague_end}")