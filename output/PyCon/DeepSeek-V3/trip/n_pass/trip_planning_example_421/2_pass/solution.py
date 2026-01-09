import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    required_days = {
        "Nice": 5,
        "Krakow": 6, 
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }
    
    # Direct flight connections
    connections = {
        "Nice": ["Dublin", "Frankfurt", "Lyon"],
        "Dublin": ["Nice", "Frankfurt", "Krakow", "Lyon"],
        "Frankfurt": ["Dublin", "Krakow", "Lyon", "Nice"],
        "Krakow": ["Dublin", "Frankfurt"],
        "Lyon": ["Frankfurt", "Dublin", "Nice"]
    }
    
    # Total days
    total_days = 20
    
    # Variables for city order
    positions = list(range(5))
    problem.addVariables(positions, cities)
    problem.addConstraint(AllDifferentConstraint())
    
    # Connection constraints between consecutive cities
    for i in range(4):
        def connected_constraint(city1, city2, i=i):
            return city2 in connections.get(city1, [])
        problem.addConstraint(connected_constraint, [i, i+1])
    
    # Find all valid city sequences
    city_sequences = problem.getSolutions()
    
    if not city_sequences:
        print(json.dumps({"error": "No valid city sequence found"}))
        return
    
    # Convert solutions to sequences
    sequences = []
    for sol in city_sequences:
        sequence = [sol[i] for i in range(5)]
        sequences.append(sequence)
    
    # Now try to assign days to each sequence
    valid_itineraries = []
    
    for sequence in sequences:
        # Try to assign start days to each city
        start_days = {}
        end_days = {}
        
        # Nice must be between day 1-5, so it must start on day 1
        nice_pos = sequence.index("Nice")
        start_days["Nice"] = 1
        end_days["Nice"] = 1 + required_days["Nice"] - 1
        
        # Frankfurt must be between day 19-20, so it must start on day 19
        frankfurt_pos = sequence.index("Frankfurt")
        start_days["Frankfurt"] = 19
        end_days["Frankfurt"] = 19 + required_days["Frankfurt"] - 1
        
        # For other cities, we need to find valid start days that don't overlap
        # and respect the travel sequence
        
        # We'll work with the sequence order to assign days
        current_day = 1
        
        for i, city in enumerate(sequence):
            if city in start_days:  # Already assigned (Nice or Frankfurt)
                if start_days[city] < current_day:
                    # This city should have been visited earlier in the sequence
                    # but its assigned days conflict with the sequence order
                    break
                current_day = end_days[city] + 1
            else:
                # Assign the next available days for this city
                days_needed = required_days[city]
                start_days[city] = current_day
                end_days[city] = current_day + days_needed - 1
                current_day = end_days[city] + 1
        
        # Check if all constraints are satisfied
        if len(start_days) == 5:
            # Verify Nice constraint
            if not (start_days["Nice"] == 1 and end_days["Nice"] == 5):
                continue
            
            # Verify Frankfurt constraint
            if not (start_days["Frankfurt"] == 19 and end_days["Frankfurt"] == 20):
                continue
            
            # Verify no overlaps and correct total days
            all_days = set()
            valid_schedule = True
            
            for city in cities:
                city_days = set(range(start_days[city], end_days[city] + 1))
                if all_days & city_days:  # Overlap detected
                    valid_schedule = False
                    break
                all_days.update(city_days)
            
            # Check if we used exactly 20 days (1-20 inclusive)
            if valid_schedule and max(all_days) == 20 and min(all_days) == 1:
                # Verify the sequence order matches day assignments
                sequence_valid = True
                for i in range(4):
                    city1, city2 = sequence[i], sequence[i+1]
                    if end_days[city1] >= start_days[city2]:
                        sequence_valid = False
                        break
                
                if sequence_valid:
                    valid_itineraries.append((sequence, start_days, end_days))
    
    if not valid_itineraries:
        print(json.dumps({"error": "No valid itinerary satisfying all constraints"}))
        return
    
    # Use the first valid itinerary
    sequence, start_days, end_days = valid_itineraries[0]
    
    # Build the itinerary in order
    itinerary = []
    for city in sequence:
        day_range = f"Day {start_days[city]}-{end_days[city]}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()