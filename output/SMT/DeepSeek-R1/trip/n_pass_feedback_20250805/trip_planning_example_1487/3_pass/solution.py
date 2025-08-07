from z3 import *
import json

def main():
    # Define cities and their stay durations
    city_list = ['Athens', 'Brussels', 'Copenhagen', 'Dubrovnik', 'Geneva', 'Munich', 'Naples', 'Prague', 'Santorini']
    durations = [4, 4, 5, 3, 3, 5, 4, 2, 5]  # Corresponding to city_list
    
    # Indexes for cities with event constraints
    copenhagen_idx = city_list.index('Copenhagen')
    naples_idx = city_list.index('Naples')
    athens_idx = city_list.index('Athens')
    
    # Define direct flights
    flight_strings = [
        "Copenhagen and Dubrovnik", "Brussels and Copenhagen", "Prague and Geneva", "Athens and Geneva",
        "Naples and Dubrovnik", "Athens and Dubrovnik", "Geneva and Mykonos", "Naples and Mykonos",
        "Naples and Copenhagen", "Munich and Mykonos", "Naples and Athens", "Prague and Athens",
        "Santorini and Geneva", "Athens and Santorini", "Naples and Munich", "Prague and Copenhagen",
        "Brussels and Naples", "Athens and Mykonos", "Athens and Copenhagen", "Naples and Geneva",
        "Dubrovnik and Munich", "Brussels and Munich", "Prague and Brussels", "Brussels and Athens",
        "Athens and Munich", "Geneva and Munich", "Copenhagen and Munich", "Brussels and Geneva",
        "Copenhagen and Geneva", "Prague and Munich", "Copenhagen and Santorini", "Naples and Santorini",
        "Geneva and Dubrovnik"
    ]
    
    # Create flight connection set
    flight_set = set()
    for s in flight_strings:
        cities = s.split(' and ')
        if len(cities) == 2:
            a, b = cities[0].strip(), cities[1].strip()
            flight_set.add((a, b))
            flight_set.add((b, a))
    
    # Precompute allowed connections between cities
    allowed_connections = set()
    for i in range(len(city_list)):
        for j in range(len(city_list)):
            if i != j and (city_list[i], city_list[j]) in flight_set:
                allowed_connections.add((i, j))
    
    # Cities that can fly to Mykonos
    mykonos_connections = [i for i, city in enumerate(city_list) 
                          if (city, 'Mykonos') in flight_set]
    
    # Initialize solver
    s = Solver()
    
    # Position variables: 9 positions for the cities
    x = [[Bool(f'x_{i}_{j}') for j in range(len(city_list))] for i in range(9)]
    
    # Each position has exactly one city
    for i in range(9):
        s.add(Sum([If(x[i][j], 1, 0) for j in range(len(city_list))]) == 1)
    
    # Each city appears in exactly one position
    for j in range(len(city_list)):
        s.add(Sum([If(x[i][j], 1, 0) for i in range(9)]) == 1)
    
    # Flight constraints between consecutive cities
    for pos in range(8):
        valid_transitions = []
        for i in range(len(city_list)):
            for j in range(len(city_list)):
                if (i, j) in allowed_connections:
                    valid_transitions.append(And(x[pos][i], x[pos+1][j]))
        s.add(Or(valid_transitions))
    
    # Constraint: last city must connect to Mykonos
    last_city_constraint = []
    for city_idx in mykonos_connections:
        last_city_constraint.append(x[8][city_idx])
    s.add(Or(last_city_constraint))
    
    # Symbolic durations for each position
    position_durations = [Int(f'dur_{i}') for i in range(9)]
    for i in range(9):
        s.add(position_durations[i] == Sum([If(x[i][j], durations[j], 0) for j in range(len(city_list))]))
    
    # Cumulative start days (accounting for flight day overlaps)
    cumulative_days = [Int(f'cumul_{i}') for i in range(10)]
    s.add(cumulative_days[0] == 0)
    for i in range(1, 10):
        s.add(cumulative_days[i] == cumulative_days[i-1] + position_durations[i-1] - 1)
    
    # Start and end days for each city
    start_days = [1 + cumulative_days[i] for i in range(9)]
    end_days = [start_days[i] + position_durations[i] - 1 for i in range(9)]
    
    # Event constraints
    for pos in range(9):
        # Copenhagen must include a day between 11 and 15
        s.add(Implies(x[pos][copenhagen_idx], 
                     And(start_days[pos] <= 15, end_days[pos] >= 11)))
        # Naples must include a day between 5 and 8
        s.add(Implies(x[pos][naples_idx], 
                     And(start_days[pos] <= 8, end_days[pos] >= 5)))
        # Athens must include a day between 8 and 11
        s.add(Implies(x[pos][athens_idx], 
                     And(start_days[pos] <= 11, end_days[pos] >= 8)))
    
    # Mykonos must start on day 27 (to include 27 and 28)
    s.add(cumulative_days[9] == 26)  # Ensures Mykonos starts on day 27
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        itinerary = []
        for i in range(9):
            for j in range(len(city_list)):
                if is_true(m.evaluate(x[i][j])):
                    start = m.evaluate(start_days[i]).as_long()
                    end = m.evaluate(end_days[i]).as_long()
                    itinerary.append({
                        'city': city_list[j],
                        'start_day': start,
                        'end_day': end
                    })
                    break
        
        # Add Mykonos (fixed at days 27-28)
        itinerary.append({
            'city': 'Mykonos',
            'start_day': 27,
            'end_day': 28
        })
        
        # Format day ranges as strings
        formatted_itinerary = []
        for stay in itinerary:
            start, end = stay['start_day'], stay['end_day']
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            formatted_itinerary.append({
                'day_range': day_range,
                'place': stay['city']
            })
        
        print(json.dumps({'itinerary': formatted_itinerary}, indent=2))
    else:
        print("No valid itinerary found")

if __name__ == "__main__":
    main()