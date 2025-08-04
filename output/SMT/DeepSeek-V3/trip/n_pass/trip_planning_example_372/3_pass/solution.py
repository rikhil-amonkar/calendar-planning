from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Cities: Madrid (0), Porto (1), Seville (2), Stuttgart (3)
    cities = ['Madrid', 'Porto', 'Seville', 'Stuttgart']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}

    # Define the flight connections as a set of tuples
    connections = [
        (city_to_idx['Porto'], city_to_idx['Stuttgart']),
        (city_to_idx['Seville'], city_to_idx['Porto']),
        (city_to_idx['Madrid'], city_to_idx['Porto']),
        (city_to_idx['Madrid'], city_to_idx['Seville'])
    ]
    # Make connections bidirectional
    bidirectional_connections = []
    for a, b in connections:
        bidirectional_connections.append((a, b))
        bidirectional_connections.append((b, a))
    connections_set = set(bidirectional_connections)

    # Variables: For each day, which city is visited (and possibly a second city if it's a flight day)
    # We represent each day as a list of possible cities (at most two)
    max_days = 13
    itinerary = [[Int(f'day_{day}_city_0'), Int(f'day_{day}_city_1')] for day in range(1, max_days + 1)]

    # Constraints for each day:
    for day in range(1, max_days + 1):
        day_idx = day - 1
        # The first city of the day must be valid (0-3)
        s.add(And(itinerary[day_idx][0] >= 0, itinerary[day_idx][0] <= 3))
        # The second city can be -1 (indicating no flight) or a valid city connected to the first city
        s.add(Or(
            itinerary[day_idx][1] == -1,
            And(
                itinerary[day_idx][1] >= 0,
                itinerary[day_idx][1] <= 3,
                (itinerary[day_idx][0], itinerary[day_idx][1]) in connections_set
            )
        ))
        # If day is a flight day (city1 != -1), then city0 != city1
        s.add(Implies(itinerary[day_idx][1] != -1, itinerary[day_idx][0] != itinerary[day_idx][1]))

    # Constraints for the stays:
    # Madrid: 4 days, including days 1-4
    for day in [1, 2, 3, 4]:
        day_idx = day - 1
        s.add(itinerary[day_idx][0] == city_to_idx['Madrid'])
        s.add(itinerary[day_idx][1] == -1)  # No flights on days 1-4 to ensure full days in Madrid

    # Total Madrid days: count days where Madrid is city0 or city1
    madrid_days = Sum([If(Or(itinerary[day][0] == city_to_idx['Madrid'], itinerary[day][1] == city_to_idx['Madrid']), 1, 0) for day in range(max_days)])
    s.add(madrid_days == 4)

    # Stuttgart: 7 days, including days 7 and 13
    for day in [7, 13]:
        day_idx = day - 1
        s.add(Or(
            itinerary[day_idx][0] == city_to_idx['Stuttgart'],
            itinerary[day_idx][1] == city_to_idx['Stuttgart']
        ))
    stuttgart_days = Sum([If(Or(itinerary[day][0] == city_to_idx['Stuttgart'], itinerary[day][1] == city_to_idx['Stuttgart']), 1, 0) for day in range(max_days)])
    s.add(stuttgart_days == 7)

    # Porto: 3 days
    porto_days = Sum([If(Or(itinerary[day][0] == city_to_idx['Porto'], itinerary[day][1] == city_to_idx['Porto']), 1, 0) for day in range(max_days)])
    s.add(porto_days == 3)

    # Seville: 2 days
    seville_days = Sum([If(Or(itinerary[day][0] == city_to_idx['Seville'], itinerary[day][1] == city_to_idx['Seville']), 1, 0) for day in range(max_days)])
    s.add(seville_days == 2)

    # Day 1 starts in Madrid (city0 is Madrid)
    s.add(itinerary[0][0] == city_to_idx['Madrid'])

    # The itinerary must be contiguous in terms of city visits (no impossible flights)
    # For each day after the first, the first city of the day must be either:
    # - the same as the last city of the previous day (no flight), or
    # - the second city of the previous day (if there was a flight)
    for day in range(1, max_days):
        prev_day = day - 1
        s.add(Or(
            itinerary[day][0] == itinerary[prev_day][0],
            And(itinerary[prev_day][1] != -1, itinerary[day][0] == itinerary[prev_day][1])
        ))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Construct the itinerary
        result = {'itinerary': []}
        for day in range(1, max_days + 1):
            day_idx = day - 1
            city0 = m[itinerary[day_idx][0]].as_long()
            city1 = m[itinerary[day_idx][1]].as_long()
            cities_in_day = [cities[city0]]
            if city1 != -1:
                cities_in_day.append(cities[city1])
            result['itinerary'].append({'day': day, 'cities': cities_in_day})
        return result
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(itinerary)
else:
    print("No valid itinerary found.")