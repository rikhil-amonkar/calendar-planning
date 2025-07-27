from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Cities: Prague, Berlin, Tallinn, Stockholm
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}

    # Define variables for each day (1..12), representing the city on that day
    days = [Int(f"day_{i}") for i in range(1, 13)]
    for day in days:
        s.add(day >= 0, day < len(cities))

    # Direct flights: adjacency list
    adjacency = {
        'Berlin': ['Tallinn', 'Stockholm'],
        'Prague': ['Tallinn', 'Stockholm'],
        'Tallinn': ['Berlin', 'Prague', 'Stockholm'],
        'Stockholm': ['Berlin', 'Prague', 'Tallinn']
    }

    # Flight constraints: consecutive days must be either same city or connected by a direct flight
    for i in range(11):
        day_current = days[i]
        day_next = days[i+1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            day_current == day_next,
            Or([And(day_current == city_to_int[a], day_next == city_to_int[b]) 
                for a in adjacency for b in adjacency[a]])
        ))

    # Total days per city constraints
    # Prague: 2 days
    s.add(Sum([If(d == city_to_int['Prague'], 1, 0) for d in days]) == 2)
    # Berlin: 3 days, including day 6 and 8
    s.add(Sum([If(d == city_to_int['Berlin'], 1, 0) for d in days]) == 3)
    s.add(days[5] == city_to_int['Berlin'])  # day 6 is index 5
    s.add(days[7] == city_to_int['Berlin'])  # day 8 is index 7
    # Tallinn: 5 days, between day 8 and 12 (inclusive)
    # So from day 8 (index 7) to day 12 (index 11), at least some days must be Tallinn, totaling 5
    s.add(Sum([If(days[i] == city_to_int['Tallinn'], 1, 0) for i in range(7, 12)]) >= 1)  # At least one day between 8-12 is Tallinn
    s.add(Sum([If(d == city_to_int['Tallinn'], 1, 0) for d in days]) == 5)
    # Stockholm: 5 days
    s.add(Sum([If(d == city_to_int['Stockholm'], 1, 0) for d in days]) == 5)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": day_num, "place": city})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the solution
solution = solve_itinerary()
print(solution)