if s.check() == sat:
    model = s.model()
    # Extract the order as strings
    order_result = [model[order[i]].decl().name() for i in range(7)]  # ✅ Corrected line
    # Compute start and end days for each city
    itinerary = []
    for i in range(7):
        city_name = order_result[i]
        start_day = model[start_days[i]].as_long()
        end_day = start_day + durations_str[city_name] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_name
        })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")