def generate_itinerary(route, durations, total_days):
    itinerary = []
    current_day = 1
    for i in range(len(route)):
        city = route[i]
        dur = durations[i]
        start = current_day
        end = current_day + dur - 1
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary.append({
            "day_range": day_range_str,
            "place": city
        })
        current_day = end + 1
    return {"itinerary": itinerary}