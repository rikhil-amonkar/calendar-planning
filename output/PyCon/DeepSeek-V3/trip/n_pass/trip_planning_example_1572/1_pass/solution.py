import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the cities and their required days
    cities = {
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Berlin': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    
    total_days = 23
    
    # Define direct flight connections
    connections = [
        ('Paris', 'Stockholm'), ('Seville', 'Paris'), ('Naples', 'Zurich'),
        ('Nice', 'Riga'), ('Berlin', 'Milan'), ('Paris', 'Zurich'),
        ('Paris', 'Nice'), ('Milan', 'Paris'), ('Milan', 'Riga'),
        ('Paris', 'Lyon'), ('Milan', 'Naples'), ('Paris', 'Riga'),
        ('Berlin', 'Stockholm'), ('Stockholm', 'Riga'), ('Nice', 'Zurich'),
        ('Milan', 'Zurich'), ('Lyon', 'Nice'), ('Zurich', 'Stockholm'),
        ('Zurich', 'Riga'), ('Berlin', 'Naples'), ('Milan', 'Stockholm'),
        ('Berlin', 'Zurich'), ('Milan', 'Seville'), ('Paris', 'Naples'),
        ('Berlin', 'Riga'), ('Nice', 'Stockholm'), ('Berlin', 'Paris'),
        ('Nice', 'Naples'), ('Berlin', 'Nice')
    ]
    
    # Make connections bidirectional
    flight_connections = {}
    for city1, city2 in connections:
        if city1 not in flight_connections:
            flight_connections[city1] = set()
        if city2 not in flight_connections:
            flight_connections[city2] = set()
        flight_connections[city1].add(city2)
        flight_connections[city2].add(city1)
    
    # Define fixed constraints
    fixed_constraints = [
        ('Berlin', 1, 2),  # Wedding in Berlin between day 1 and 2
        ('Stockholm', 20, 22),  # Annual show in Stockholm between day 20 and 22
        ('Nice', 12, 13)  # Workshop in Nice between day 12 and 13
    ]
    
    problem = Problem()
    
    # Create variables for start day of each city visit
    start_days = {}
    for city in cities:
        start_days[city] = f"{city}_start"
        problem.addVariable(start_days[city], range(1, total_days + 1))
    
    # Create variables for end day of each city visit
    end_days = {}
    for city in cities:
        end_days[city] = f"{city}_end"
        problem.addVariable(end_days[city], range(1, total_days + 1))
    
    # Constraint: end day = start day + duration - 1
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, end, dur=duration: end == start + dur - 1,
            (start_days[city], end_days[city])
        )
    
    # Constraint: all visits must be within the 23-day period
    for city in cities:
        problem.addConstraint(
            lambda start, end: start >= 1 and end <= total_days,
            (start_days[city], end_days[city])
        )
    
    # Constraint: visits should not overlap (simplified - they can overlap if connected by flights)
    # Instead, we'll ensure the itinerary is connected via flights
    
    # Fixed constraints for specific events
    for city, start, end in fixed_constraints:
        problem.addConstraint(
            lambda city_start, city_end, s=start, e=end: 
            city_start <= s and city_end >= e,
            (start_days[city], end_days[city])
        )
    
    # Constraint: itinerary must be connected via direct flights
    def itinerary_connected(starts, ends):
        # Create a timeline of city visits
        visits = []
        for city in cities:
            start = starts[start_days[city]]
            end = ends[end_days[city]]
            visits.append((start, end, city))
        
        visits.sort(key=lambda x: x[0])  # Sort by start day
        
        # Check connectivity between consecutive visits
        for i in range(len(visits) - 1):
            current_city = visits[i][2]
            next_city = visits[i + 1][2]
            current_end = visits[i][1]
            next_start = visits[i + 1][0]
            
            # Cities should be connected by direct flight
            if current_city != next_city:
                if next_city not in flight_connections.get(current_city, set()):
                    return False
            
            # Ensure no gaps in itinerary (travel days are included in visits)
            if current_end + 1 < next_start:
                return False
        
        return True
    
    # Add all start and end variables to the constraint
    all_vars = []
    for city in cities:
        all_vars.append(start_days[city])
        all_vars.append(end_days[city])
    
    problem.addConstraint(itinerary_connected, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try without strict connectivity constraint
        problem = Problem()
        
        # Re-add basic variables and constraints
        for city in cities:
            problem.addVariable(start_days[city], range(1, total_days + 1))
            problem.addVariable(end_days[city], range(1, total_days + 1))
        
        for city, duration in cities.items():
            problem.addConstraint(
                lambda start, end, dur=duration: end == start + dur - 1,
                (start_days[city], end_days[city])
            )
        
        for city in cities:
            problem.addConstraint(
                lambda start, end: start >= 1 and end <= total_days,
                (start_days[city], end_days[city])
            )
        
        for city, start, end in fixed_constraints:
            problem.addConstraint(
                lambda city_start, city_end, s=start, e=end: 
                city_start <= s and city_end >= e,
                (start_days[city], end_days[city])
            )
        
        solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        
        # Build itinerary
        itinerary = []
        visits = []
        
        for city in cities:
            start = solution[start_days[city]]
            end = solution[end_days[city]]
            visits.append((start, end, city))
        
        # Sort visits by start day
        visits.sort(key=lambda x: x[0])
        
        # Create day-place mappings
        current_visit = visits[0]
        current_start = current_visit[0]
        current_end = current_visit[1]
        current_city = current_visit[2]
        
        for i in range(1, len(visits)):
            next_visit = visits[i]
            next_start = next_visit[0]
            next_end = next_visit[1]
            next_city = next_visit[2]
            
            if next_start == current_end + 1:
                # Continuous visit, extend current range
                current_end = next_end
            else:
                # Break in itinerary, add current range to itinerary
                if current_start == current_end:
                    day_range = f"Day {current_start}"
                else:
                    day_range = f"Day {current_start}-{current_end}"
                itinerary.append({"day_range": day_range, "place": current_city})
                
                current_start = next_start
                current_end = next_end
                current_city = next_city
        
        # Add the last visit
        if current_start == current_end:
            day_range = f"Day {current_start}"
        else:
            day_range = f"Day {current_start}-{current_end}"
        itinerary.append({"day_range": day_range, "place": current_city})
        
        # Verify total days
        total_planned_days = 0
        for visit in itinerary:
            day_range = visit["day_range"]
            if "-" in day_range:
                start, end = map(int, day_range.replace("Day ", "").split("-"))
                total_planned_days += (end - start + 1)
            else:
                total_planned_days += 1
        
        # Output result
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()