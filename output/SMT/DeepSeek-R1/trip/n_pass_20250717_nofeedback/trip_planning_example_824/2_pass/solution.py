import json
from z3 import *

def main():
    # Cities and their indices
    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    n = 7

    # Durations for each city (by index)
    dur = [5, 3, 3, 5, 3, 4, 5]

    # Allowed directed flights: list of tuples (u, v)
    allowed_edges = [
        (0, 1), (1, 0),  # Berlin-Split
        (0, 3), (3, 0),  # Berlin-Riga
        (0, 4), (4, 0),  # Berlin-Lisbon
        (0, 5), (5, 0),  # Berlin-Tallinn
        (1, 6), (6, 1),  # Split-Lyon
        (2, 3), (3, 2),  # Bucharest-Riga
        (2, 4), (4, 2),  # Bucharest-Lisbon
        (3, 4), (4, 3),  # Riga-Lisbon
        (6, 2), (2, 6),  # Lyon-Bucharest
        (6, 4), (4, 6),  # Lyon-Lisbon
        (3, 5)            # Riga->Tallinn
    ]

    # Create Z3 variables for the sequence: city0, city1, ... city6
    city_vars = [Int(f'city_{i}') for i in range(n)]

    s = Solver()

    # Each city must be between 0 and 6
    for i in range(n):
        s.add(And(city_vars[i] >= 0, city_vars[i] < n))

    # All cities distinct
    s.add(Distinct(city_vars))

    # First city must be Berlin (index 0)
    s.add(city_vars[0] == 0)

    # Flight constraints for consecutive cities
    for i in range(n - 1):
        constraints = []
        for u, v in allowed_edges:
            constraints.append(And(city_vars[i] == u, city_vars[i + 1] == v))
        s.add(Or(constraints))

    # Create a Z3 array for durations
    dur_array = Array('durations', IntSort(), IntSort())
    for idx, d in enumerate(dur):
        dur_array = Store(dur_array, idx, d)

    # Build start day expressions for each position in the sequence
    start_exprs = [None] * n
    start_exprs[0] = 1
    for i in range(1, n):
        terms = []
        for j in range(i):
            term = Select(dur_array, city_vars[j]) - 1
            terms.append(term)
        start_exprs[i] = 1 + Sum(terms)

    # Constraints for Lyon (index 6) and Bucharest (index 2)
    for i in range(n):
        s.add(Implies(city_vars[i] == 6, And(start_exprs[i] >= 3, start_exprs[i] <= 11)))
        s.add(Implies(city_vars[i] == 2, And(start_exprs[i] >= 11, start_exprs[i] <= 15)))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        seq = [model[city_vars[i]].as_long() for i in range(n)]
        
        # Compute start and end days for each city in the sequence
        start_days = []
        end_days = []
        current = 1
        for i in range(n):
            city_idx = seq[i]
            duration = dur[city_idx]
            start_day = current
            end_day = current + duration - 1
            start_days.append(start_day)
            end_days.append(end_day)
            current = end_day + 1  # Next city starts the day after the current city ends (but note: flight day is shared)
            # However, note: the flight day is counted in both cities. Therefore, the next city starts on the same day the flight is taken? 
            # But our model: the start day of the next city is computed as: current start_day + (duration - 1) for the current city.
            # In our computation above, we did: current = end_day + 1 -> which is the next day. 
            # However, in the Z3 model, we computed the start day of the next city as: 1 + sum of (durations of previous cities - 1) 
            # which is equivalent to: 1 + (start_day[0]-1) + ... + (start_day[i-1]-1) 
            # But note: the end_day of the previous city is start_day[i-1] + dur[i-1] - 1, and then the next city starts at end_day? 
            # Actually, the flight day is the last day of the previous city and the first day of the next city. 
            # Therefore, the next city should start on the same day the previous city ends? 
            # But in our Z3 model, we have: 
            #   start_exprs[i] = 1 + sum_{j=0}^{i-1} (dur[j]-1)
            # and for the next city i+1: start_exprs[i+1] = 1 + sum_{j=0}^{i} (dur[j]-1) = start_exprs[i] + (dur[i]-1)
            # So the start day of city i+1 = start day of city i + (duration of city i - 1)
            # This means: the start day of city i+1 is the day after the first day of city i? 
            # But note: city i starts at day s, then it occupies days: s, s+1, ..., s+dur[i]-1.
            # Then the next city starts at s + (dur[i]-1) -> which is the last day of city i? 
            # Therefore, the next city starts on the last day of the previous city? 
            # That matches the requirement: the flight day is the last day of the current city and the first day of the next city.
            # So our computation above (current = end_day + 1) is incorrect because it sets the next city to start the day after the last day of the previous city.
            # We must instead set: current = start_day + (dur[city_idx] - 1) for the next city? 
            # But note: we are building the itinerary by the actual days. 
            # Actually, we don't need to recompute the start days in the Python code because we have the Z3 model. 
            # Instead, we can compute the start days from the model's sequence using the same formula as in Z3: 
            #   start_day[0] = 1
            #   start_day[i] = 1 + sum_{j=0}^{i-1} (dur[seq[j]] - 1)
            # Let's recompute the start days without using the Z3 expressions.
        
        # Recompute start days and end days without Z3
        start_days = [1]
        for i in range(1, n):
            prev_dur = dur[seq[i-1]]
            start_days.append(start_days[i-1] + (prev_dur - 1))
        end_days = [start_days[i] + dur[seq[i]] - 1 for i in range(n)]
        
        # Generate itinerary: for each day from 1 to 22, list all cities we are in on that day.
        itinerary_list = []
        for day in range(1, 23):  # Days 1 to 22
            for i in range(n):
                if start_days[i] <= day <= end_days[i]:
                    city_name = cities[seq[i]]
                    itinerary_list.append({"day": day, "city": city_name})
        
        # Output as JSON
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()