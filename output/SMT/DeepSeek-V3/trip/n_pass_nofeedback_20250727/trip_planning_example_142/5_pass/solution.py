from z3 import *

def solve_itinerary():
    s = Solver()

    # City mapping
    cities = {'Madrid': 0, 'Dublin': 1, 'Tallinn': 2}
    inv_cities = {v: k for k, v in cities.items()}

    # Day variables (1-7)
    days = [Int(f'day_{i}') for i in range(1, 8)]

    # Each day must be a valid city
    for day in days:
        s.add(Or(day == 0, day == 1, day == 2))

    # Flight transition constraints (only allowed direct connections)
    for i in range(6):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == 0, next_day == 1),  # Madrid -> Dublin
            And(current == 1, next_day == 0),  # Dublin -> Madrid
            And(current == 1, next_day == 2),  # Dublin -> Tallinn
            And(current == 2, next_day == 1)   # Tallinn -> Dublin
        ))

    # Calculate days spent in each city (counting flight days for both cities)
    madrid_days = 0
    dublin_days = 0
    tallinn_days = 0
    
    # First day counts fully
    madrid_days += If(days[0] == 0, 1, 0)
    dublin_days += If(days[0] == 1, 1, 0)
    tallinn_days += If(days[0] == 2, 1, 0)
    
    # Subsequent days count fully unless it's a flight day
    for i in range(1, 7):
        # If we changed cities, count for both
        if i > 0 and days[i] != days[i-1]:
            madrid_days += If(days[i] == 0, 1, 0)
            dublin_days += If(days[i] == 1, 1, 0)
            tallinn_days += If(days[i] == 2, 1, 0)
            # Also count previous city
            madrid_days += If(days[i-1] == 0, 1, 0)
            dublin_days += If(days[i-1] == 1, 1, 0)
            tallinn_days += If(days[i-1] == 2, 1, 0)
        else:
            # Normal day, count once
            madrid_days += If(days[i] == 0, 1, 0)
            dublin_days += If(days[i] == 1, 1, 0)
            tallinn_days += If(days[i] == 2, 1, 0)

    # Total days constraints (adjusted for flight days)
    s.add(madrid_days == 4)
    s.add(dublin_days == 3)
    s.add(tallinn_days == 2)

    # Workshop constraint (must be in Tallinn on day 6 or 7)
    s.add(Or(days[5] == 2, days[6] == 2))

    # Additional constraints to guide the solver
    # Start in Madrid (most flexible starting point)
    s.add(days[0] == 0)
    
    # Ensure we don't have consecutive Tallinn days (since we only have 2 days)
    for i in range(5):
        s.add(Not(And(days[i] == 2, days[i+1] == 2)))

    # Solve and return the itinerary
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(7):
            day_num = i + 1
            city_code = model.evaluate(days[i]).as_long()
            city_name = inv_cities[city_code]
            itinerary.append({'day': day_num, 'place': city_name})
        
        # Verify the solution meets all constraints
        madrid_count = sum(1 for day in itinerary if day['place'] == 'Madrid')
        dublin_count = sum(1 for day in itinerary if day['place'] == 'Dublin')
        tallinn_count = sum(1 for day in itinerary if day['place'] == 'Tallinn')
        
        # Count flight days properly
        for i in range(1, 7):
            if itinerary[i]['place'] != itinerary[i-1]['place']:
                # Flight day - count for both cities
                if itinerary[i-1]['place'] == 'Madrid':
                    madrid_count += 1
                elif itinerary[i-1]['place'] == 'Dublin':
                    dublin_count += 1
                elif itinerary[i-1]['place'] == 'Tallinn':
                    tallinn_count += 1
                
                if itinerary[i]['place'] == 'Madrid':
                    madrid_count += 1
                elif itinerary[i]['place'] == 'Dublin':
                    dublin_count += 1
                elif itinerary[i]['place'] == 'Tallinn':
                    tallinn_count += 1
        
        # Verify counts
        if (madrid_count == 4 and dublin_count == 3 and tallinn_count == 2 and
            (itinerary[5]['place'] == 'Tallinn' or itinerary[6]['place'] == 'Tallinn')):
            return {'itinerary': itinerary}
        else:
            return {'error': 'Found invalid solution'}
    else:
        return {'error': 'No valid itinerary found'}

# Output the solution
import json
solution = solve_itinerary()
print(json.dumps(solution, indent=2))