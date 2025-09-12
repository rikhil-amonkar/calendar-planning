if solver.check() == sat:
    model = solver.model()
    cities_order_vals = [str(model.evaluate(c)) for c in cities_order]
    start_day_vals = [model.evaluate(s).as_long() for s in start_day]
    end_day_vals = [model.evaluate(e).as_long() for e in end_day]
    
    # Generate itinerary
    itinerary = []
    for i in range(8):
        city = cities_order_vals[i]
        start = start_day_vals[i]
        end = end_day_vals[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")