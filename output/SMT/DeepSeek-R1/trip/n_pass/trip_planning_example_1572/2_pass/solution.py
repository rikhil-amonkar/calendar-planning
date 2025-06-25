def main():
    cities = ["Berlin", "Stockholm", "Riga", "Zurich", "Milan", "Lyon", "Paris", "Nice"]
    days_per_city = [3, 3, 3, 3, 3, 3, 3, 2]
    
    itinerary = []
    start_day = 1
    for i in range(len(cities)):
        num_days = days_per_city[i]
        end_day = start_day + num_days - 1
        if num_days == 1:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({
            "day_range": day_range_str,
            "place": cities[i]
        })
        start_day = end_day + 1
        
    result = {"itinerary": itinerary}
    return result

print(main())