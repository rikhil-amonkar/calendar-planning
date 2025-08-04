def parse_day(day_range):
    parts = day_range.split('-')
    start_day = int(parts[0].split()[1])
    # Check if there is a second part to the day range
    end_day = int(parts[1].split()[1]) if len(parts) > 1 else start_day
    return start_day, end_day