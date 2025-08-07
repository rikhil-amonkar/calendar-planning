import z3

def main():
    cities = ["Brussels", "Venice", "Santorini", "Lisbon", "Reykjavik", "London", "Madrid"]
    c2i = {c: i for i, c in enumerate(cities)}
    
    # Create flight matrix (7x7 boolean matrix)
    flight_matrix = [[False]*7 for _ in range(7)]
    # Allow staying in same city
    for i in range(7):
        flight_matrix[i][i] = True
    
    # Add bidirectional flights
    for a, b in [
        ("Venice", "Madrid"), ("Lisbon", "Reykjavik"), ("Brussels", "Venice"),
        ("Venice", "Santorini"), ("Lisbon", "Venice"), ("Brussels", "London"),
        ("Madrid", "London"), ("Santorini", "London"), ("London", "Reykjavik"),
        ("Brussels", "Lisbon"), ("Lisbon", "London"), ("Lisbon", "Madrid"),
        ("Madrid", "Santorini"), ("Brussels", "Reykjavik"), ("Brussels", "Madrid"),
        ("Venice", "London")
    ]:
        i, j = c2i[a], c2i[b]
        flight_matrix[i][j] = True
        flight_matrix[j][i] = True
    
    # Add unidirectional flight
    flight_matrix[c2i["Reykjavik"]][c2i["Madrid"]] = True
    
    # Required days per city
    days_req = [0]*7
    for city, days in [
        ("Brussels", 2), ("Venice", 3), ("Santorini", 3),
        ("Lisbon", 4), ("Reykjavik", 3), ("London", 3), ("Madrid", 5)
    ]:
        days_req[c2i[city]] = days

    solver = z3.Solver()
    # City at end of each day (17 days)
    c = [z3.Int(f"d{i}") for i in range(17)]
    
    # Constraint 1: All cities must be valid (0-6)
    for city_var in c:
        solver.add(z3.And(city_var >= 0, city_var < 7))
    
    # Constraint 2: Conference in Brussels (days 1-2)
    solver.add(c[0] == c2i["Brussels"])
    solver.add(c[1] == c2i["Brussels"])
    
    # Constraint 3: Wedding in Madrid (days 7-11)
    for day in range(6, 11):  # Days 6-10 (0-indexed) = days 7-11
        solver.add(z3.Or(c[day] == c2i["Madrid"], c[day-1] == c2i["Madrid"]))
    
    # Constraint 4: Visit Venice between days 5-7
    solver.add(z3.Or(
        c[3] == c2i["Venice"],  # Day 5 start
        c[4] == c2i["Venice"],  # Day 5 end / Day 6 start
        c[5] == c2i["Venice"],  # Day 6 end / Day 7 start
        c[6] == c2i["Venice"]   # Day 7 end
    ))
    
    # Constraint 5: Flight transitions
    for i in range(17):
        prev_city = c[i-1] if i > 0 else c2i["Brussels"]
        solver.add(flight_matrix[prev_city.as_long()][c[i].as_long()])
    
    # Constraint 6: Count days per city
    for city_idx in range(7):
        if days_req[city_idx] == 0:
            continue
            
        count = 0
        # Day 0: Start in Brussels, end at c[0]
        if city_idx == c2i["Brussels"]:
            count += 1  # Start of day 1 in Brussels
        if c[0].as_long() == city_idx:
            count += 1  # End of day 1
            
        for i in range(1, 17):
            if c[i-1].as_long() == city_idx:
                count += 1  # Start of day i+1
            if c[i].as_long() == city_idx:
                count += 1  # End of day i+1
                
        solver.add(count == days_req[city_idx] * 2)
    
    # Solve and output
    if solver.check() == z3.sat:
        m = solver.model()
        itinerary = []
        for i in range(17):
            city_idx = m.evaluate(c[i]).as_long()
            itinerary.append({"day": i+1, "place": cities[city_idx]})
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()