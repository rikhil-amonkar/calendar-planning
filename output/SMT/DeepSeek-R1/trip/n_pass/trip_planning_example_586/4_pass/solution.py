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
    
    def parse_day_range(day_range_str):
        parts = day_range_str.replace('Day ', '').split('-')
        start = int(parts[0])
        end = int(parts[1]) if len(parts) > 1 else start
        return (start, end)
    
    city_segments = {}
    for item in input_itinerary["itinerary"]:
        place = item["place"]
        s, e = parse_day_range(item["day_range"])
        if place not in city_segments:
            city_segments[place] = []
        city_segments[place].append((s, e))
    
    assignment = [None] * 13  # Index 0 unused, days 1 to 12
    
    for day in range(1, 13):
        candidates = []
        for city, seg_list in city_segments.items():
            max_end = -1
            min_start = float('inf')
            for (s, e) in seg_list:
                if s <= day <= e:
                    if e > max_end:
                        max_end = e
                        min_start = s
                    elif e == max_end:
                        if s < min_start:
                            min_start = s
            if max_end != -1:
                candidates.append((max_end, min_start, city))
        if not candidates:
            raise RuntimeError(f"No candidate found for day {day}")
        candidates.sort(key=lambda x: (-x[0], x[1], x[2]))
        chosen_city = candidates[0][2]
        assignment[day] = chosen_city
    
    itinerary = []
    current_city = assignment[1]
    start_day = 1
    for day in range(2, 13):
        if assignment[day] == current_city:
            continue
        else:
            end_day = day - 1
            day_range_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range_str, "place": current_city})
            current_city = assignment[day]
            start_day = day
    if start_day <= 12:
        end_day = 12
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": current_city})
    
    result = {"itinerary": itinerary}
    return result

if __name__ == '__main__':
    result = main()
    print(result)