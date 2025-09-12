# ... [previous code unchanged] ...

if s.check() == sat:
    model = s.model()
    # Extract the itinerary sequence
    itinerary = [model.evaluate(itin[i]) for i in range(7)]
    # Now compute the day ranges
    durations = {
        Berlin: 3,
        Barcelona: 2,
        Lyon: 2,
        Nice: 5,
        Athens: 5,
        Stockholm: 5,
        Vilnius: 4,
    }
    result = []
    start_day = 1
    for city in itinerary:
        dur = durations[city]
        end_day = start_day + dur - 1
        result.append({
            'day_range': f"Day {start_day}-{end_day}",
            'place': str(city)  # Fixed: use str(city)
        })
        start_day = end_day  # Next city starts on this day

    output = {"itinerary": result}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")