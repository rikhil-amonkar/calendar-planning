from z3 import *

def solve_itinerary():
    # Create solver instance
    s = Solver()

    # Define cities and mappings
    cities = ['Split', 'Santorini', 'London']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}

    # Total days
    total_days = 18

    # Create variables for each day's location
    day_location = [Int(f'day_{i}_loc') for i in range(1, total_days + 1)]

    # Each day's location must be valid
    for day in day_location:
        s.add(day >= 0, day <= 2)

    # Days in each city
    split_days = 6
    santorini_days = 7
    london_days = 7

    # Count days in each city
    split_count = Sum([If(day_location[i] == city_to_int['Split'], 1, 0) for i in range(total_days)])
    santorini_count = Sum([If(day_location[i] == city_to_int['Santorini'], 1, 0) for i in range(total_days)])
    london_count = Sum([If(day_location[i] == city_to_int['London'], 1, 0) for i in range(total_days)])

    s.add(split_count == split_days)
    s.add(santorini_count == santorini_days)
    s.add(london_count == london_days)

    # Conference days must be in Santorini
    s.add(day_location[11] == city_to_int['Santorini'])  # Day 12
    s.add(day_location[17] == city_to_int['Santorini'])  # Day 18

    # Flight constraints
    for i in range(total_days - 1):
        current = day_location[i]
        next_day = day_location[i + 1]
        # Allowed transitions:
        # Same city
        # Split <-> London
        # London <-> Santorini
        s.add(Or(
            current == next_day,
            And(current == city_to_int['Split'], next_day == city_to_int['London']),
            And(current == city_to_int['London'], next_day == city_to_int['Split']),
            And(current == city_to_int['London'], next_day == city_to_int['Santorini']),
            And(current == city_to_int['Santorini'], next_day == city_to_int['London'])
        ))

    # Start in Santorini to satisfy day 12
    s.add(day_location[0] == city_to_int['Santorini'])

    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Build itinerary
        current_place = None
        start_day = 1
        for day in range(1, total_days + 1):
            loc = model[day_location[day - 1]].as_long()
            place = int_to_city[loc]
            
            if day == 1:
                current_place = place
                start_day = 1
            else:
                if place != current_place:
                    # Add previous stay
                    if start_day == day - 1:
                        itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
                    else:
                        itinerary.append({'day_range': f'Day {start_day}-{day - 1}', 'place': current_place})
                    # Add flight day (both departure and arrival)
                    itinerary.append({'day_range': f'Day {day}', 'place': current_place})
                    itinerary.append({'day_range': f'Day {day}', 'place': place})
                    current_place = place
                    start_day = day
        
        # Add last stay
        if start_day == total_days:
            itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
        else:
            itinerary.append({'day_range': f'Day {start_day}-{total_days}', 'place': current_place})

        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate itinerary
itinerary = solve_itinerary()
print(itinerary)