# Check for a satisfying assignment
if s.check() == sat:
    model = s.model()
    city_order = [str(model[order[i]]) for i in range(4)]
    start_values = [model[start_days[i]].as_long() for i in range(4)]
    end_values = [model[end_days[i]].as_long() for i in range(4)]

    itinerary = []
    for i in range(4):
        city = city_order[i]
        start = start_values[i]
        end = end_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))