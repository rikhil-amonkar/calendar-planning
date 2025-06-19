def main():
    input_itinerary = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Prague"},
            {"day_range": "Day 2", "place": "Helsinki"},
            {"day_range": "Day 2-5", "place": "Helsinki"},
            {"day_range": "Day 2", "place": "Prague"},
            {"day_range": "Day 5", "place": "Helsinki"},
            {"day_range": "Day 5", "place": "Naples"},
            {"day_range": "Day 5-8", "place": "Naples"},
            {"day_range": "Day 8", "place": "Frankfurt"},
            {"day_range": "Day 8-10", "place": "Frankfurt"},
            {"day_range": "Day 8", "place": "Naples"},
            {"day_range": "Day 10", "place": "Frankfurt"},
            {"day_range": "Day 10", "place": "Lyon"},
            {"day_range": "Day 10-12", "place": "Lyon"}
        ]
    }
    
    segments = []
    for item in input_itinerary["itinerary"]:
        day_range_str = item["day_range"]
        place = item["place"]
        if day_range_str.startswith('Day '):
            day_str = day_range_str[4:]
            if '-' in day_str:
                parts = day_str.split('-')
                start = int(parts[0])
                end = int(parts[1])
            else:
                start = end = int(day_str)
            segments.append((start, end, place))
    
    assignment = [None] * 13  # index 0 unused, days 1 to 12
    for day in range(1, 13):
        candidates = []
        for s, e, city in segments:
            if s <= day <= e:
                candidates.append((e, s, city))
        if not candidates:
            raise RuntimeError(f"No segment covers day {day}")
        candidates.sort(key=lambda x: (-x[0], x[1], x[2]))
        chosen_city = candidates[0][2]
        assignment[day] = chosen_city
    
    grouped = []
    current_city = assignment[1]
    start_day = 1
    for day in range(2, 13):
        if assignment[day] == current_city:
            continue
        else:
            end_day = day - 1
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            grouped.append({"day_range": day_range_str, "place": current_city})
            current_city = assignment[day]
            start_day = day
    if start_day <= 12:
        end_day = 12
        if start_day == end_day:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
        grouped.append({"day_range": day_range_str, "place": current_city})
    
    result = {"itinerary": grouped}
    return result

if __name__ == '__main__':
    result = main()
    print(result)