from z3 import *

def solve_itinerary():
    s = Solver()

    # Define cities
    cities = {'Dublin': 0, 'Riga': 1, 'Vilnius': 2}
    city_names = {0: 'Dublin', 1: 'Riga', 2: 'Vilnius'}

    # Create day variables
    days = 12
    itinerary = [Int(f'day_{i}') for i in range(days)]

    # Each day must be assigned to a city
    for day in itinerary:
        s.add(Or([day == v for v in cities.values()]))

    # Flight constraints (direct flights only)
    for i in range(days - 1):
        current = itinerary[i]
        next_day = itinerary[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == cities['Dublin'], next_day == cities['Riga']),  # DUB->RIX
            And(current == cities['Riga'], next_day == cities['Dublin']),  # RIX->DUB
            And(current == cities['Riga'], next_day == cities['Vilnius']),  # RIX->VNO
            And(current == cities['Vilnius'], next_day == cities['Riga'])   # VNO->RIX
        ))

    # Count days in each city (including flight days)
    dublin_days = Sum([If(itinerary[i] == cities['Dublin'], 1, 0) for i in range(days)])
    riga_days = Sum([If(itinerary[i] == cities['Riga'], 1, 0) for i in range(days)])
    vilnius_days = Sum([If(itinerary[i] == cities['Vilnius'], 1, 0) for i in range(days)])

    # Add constraints for required days
    s.add(dublin_days == 2)
    s.add(riga_days == 5)
    s.add(vilnius_days == 7)

    # Find a solution
    if s.check() == sat:
        model = s.model()
        result = []
        for i in range(days):
            city_code = model.evaluate(itinerary[i]).as_long()
            result.append({'day': i+1, 'place': city_names[city_code]})
        return {'itinerary': result}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print itinerary
print(solve_itinerary())