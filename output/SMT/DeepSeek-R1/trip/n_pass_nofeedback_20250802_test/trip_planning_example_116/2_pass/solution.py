import z3
import json

def main():
    # Total days
    n_days = 18
    # Create variables for each day: c[0] is day1, c[17] is day18
    c = [z3.Int('c_%d' % i) for i in range(n_days)]
    solver = z3.Solver()
    
    # City constants
    Split = 0
    Santorini = 1
    London = 2
    city_names = {Split: 'Split', Santorini: 'Santorini', London: 'London'}
    
    # Each day must be one of the three cities
    for i in range(n_days):
        solver.add(z3.Or(c[i] == Split, c[i] == Santorini, c[i] == London))
    
    # Conference constraints: must be in Santorini on day12 (index11) and day18 (index17)
    solver.add(c[11] == Santorini)
    solver.add(c[17] == Santorini)
    
    # Santorini block: days 12 to 18 (indices 11 to 17)
    for i in range(11, n_days):
        solver.add(c[i] == Santorini)
    
    # No Santorini before day12 (indices 0 to 10)
    for i in range(0, 11):
        solver.add(c[i] != Santorini)
    
    # Start in Split
    solver.add(c[0] == Split)
    
    # Flight constraints: only direct flights between Split-London and London-Santorini
    for i in range(1, n_days):
        # If the city changes from day i-1 to day i, ensure it's a direct flight
        solver.add(z3.Implies(
            c[i-1] != c[i],
            z3.Or(
                z3.And(c[i-1] == Split, c[i] == London),
                z3.And(c[i-1] == London, c[i] == Split),
                z3.And(c[i-1] == London, c[i] == Santorini),
                z3.And(c[i-1] == Santorini, c[i] == London)
            )
        ))
    
    # Count end days for each city
    count_end = [0] * 3
    for city in [Split, Santorini, London]:
        count_end[city] = z3.Sum([z3.If(c[i] == city, 1, 0) for i in range(n_days)])
    
    # Count leave events for each city: when a city is left (i.e., current city is A, next is not A)
    count_leave = [0] * 3
    for city in [Split, Santorini, London]:
        # For each day from 1 to 17 (index1 to index17), check if leaving the city
        count_leave[city] = z3.Sum([z3.If(z3.And(c[i-1] == city, c[i] != city), 1, 0) for i in range(1, n_days)])
    
    # Total days in each city = end days + leave events (since flight days count for both)
    total_Split = count_end[Split] + count_leave[Split]
    total_Santorini = count_end[Santorini] + count_leave[Santorini]
    total_London = count_end[London] + count_leave[London]
    
    solver.add(total_Split == 6)
    solver.add(total_Santorini == 7)
    solver.add(total_London == 7)
    
    # We know we must be in London on day11 (index10) to fly to Santorini on day12
    solver.add(c[10] == London)
    
    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary_list = []
        for i in range(n_days):
            day = i + 1
            city_val = model.evaluate(c[i]).as_long()
            place = city_names[city_val]
            itinerary_list.append({"day": day, "place": place})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()