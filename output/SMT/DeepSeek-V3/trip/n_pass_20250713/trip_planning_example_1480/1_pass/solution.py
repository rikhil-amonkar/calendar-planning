# Reconstruct the day-by-day plan
    day_plan = []
    for day in range(27):
        city_idx = model.eval(day_city[day]).as_long()
        city = cities[city_idx]
        day_plan.append(city)
    
    itinerary = []
    i = 0
    while i < 27:
        current_city = day_plan[i]
        start_day = i + 1  # days are 1-based
        j = i + 1
        while j < 27 and day_plan[j] == current_city:
            j += 1
        end_day = j  # days are 1-based, so the range is start_day to end_day
        
        if start_day == end_day:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
        
        if j < 27:
            next_city = day_plan[j]
            # Add the flight day for both cities
            itinerary.append({"day_range": f"Day {j}", "place": current_city})
            itinerary.append({"day_range": f"Day {j}", "place": next_city})
        
        i = j
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))