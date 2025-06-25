def generate_itinerary(route, durations, total_days):
    itinerary = []
    current_day = 1
    for i in range(len(route)):
        if current_day > total_days:
            break
        dur = durations[i]
        start = current_day
        end = start + dur - 1
        if end > total_days:
            end = total_days
        if start == end:
            day_str = f"Day {start}"
        else:
            day_str = f"Day {start}-{end}"
        itinerary.append({
            "day_range": day_str,
            "place": route[i]
        })
        current_day = end + 1
    return {"itinerary": itinerary}