def generate_itinerary(route, durations, total_days):
    itinerary = []
    current_day = 1
    for i, city in enumerate(route):
        dur = durations[i]
        start = current_day
        end = start + dur - 1
        if i == len(route) - 1 or end > total_days:
            end = min(end, total_days)
        if start > total_days:
            break
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary.append({
            "day_range": day_range_str,
            "place": city
        })
        current_day = end + 1
        if current_day > total_days:
            break
    return {"itinerary": itinerary}