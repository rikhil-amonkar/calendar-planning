import json
from constraint import Problem

def main():
    # Total days and city constraints
    total_days = 12
    vilnius_days = 4
    munich_days = 3
    mykonos_days = 7
    
    # Available direct flights
    direct_flights = {
        'Vilnius': ['Munich'],
        'Munich': ['Vilnius', 'Mykonos'],
        'Mykonos': ['Munich']
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Define variables: order of cities to visit
    # We need to find a sequence of cities that satisfies the flight constraints
    cities = ['Vilnius', 'Munich', 'Mykonos']
    
    # We'll model the problem by finding a valid sequence of visits
    # Since we have 3 cities and need to visit all, we need to find the order
    
    # Try all possible permutations of the 3 cities
    from itertools import permutations
    
    valid_sequences = []
    for seq in permutations(cities):
        # Check if consecutive cities have direct flights
        valid = True
        for i in range(len(seq) - 1):
            if seq[i+1] not in direct_flights[seq[i]]:
                valid = False
                break
        if valid:
            valid_sequences.append(seq)
    
    if not valid_sequences:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # For each valid sequence, check if we can assign days to match constraints
    solution_found = False
    itinerary = []
    
    for sequence in valid_sequences:
        # Calculate day transitions
        days_remaining = total_days
        current_itinerary = []
        
        # Assign days to each city in sequence
        for i, city in enumerate(sequence):
            if city == 'Vilnius':
                days = vilnius_days
            elif city == 'Munich':
                days = munich_days
            else:  # Mykonos
                days = mykonos_days
            
            # If this is the last city, use remaining days
            if i == len(sequence) - 1:
                days = days_remaining
            
            if days > days_remaining or days <= 0:
                break
                
            start_day = total_days - days_remaining + 1
            end_day = start_day + days - 1
            current_itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            days_remaining -= days
            
        # Check if all constraints are satisfied
        if (days_remaining == 0 and 
            len(current_itinerary) == len(sequence) and
            sum(1 for item in current_itinerary if item['place'] == 'Vilnius') == 1 and
            sum(1 for item in current_itinerary if item['place'] == 'Munich') == 1 and
            sum(1 for item in current_itinerary if item['place'] == 'Mykonos') == 1):
            
            # Verify day counts
            vilnius_total = 0
            munich_total = 0
            mykonos_total = 0
            
            for item in current_itinerary:
                day_range = item['day_range']
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                days_in_city = end - start + 1
                
                if item['place'] == 'Vilnius':
                    vilnius_total += days_in_city
                elif item['place'] == 'Munich':
                    munich_total += days_in_city
                elif item['place'] == 'Mykonos':
                    mykonos_total += days_in_city
            
            if (vilnius_total == vilnius_days and 
                munich_total == munich_days and 
                mykonos_total == mykonos_days):
                itinerary = current_itinerary
                solution_found = True
                break
    
    if not solution_found:
        # Try alternative approach with constraint satisfaction
        problem = Problem()
        
        # We'll model the problem as finding start days for each city
        # Since we need to visit all cities exactly once in some order
        
        # Add variables for order positions
        problem.addVariable('first', cities)
        problem.addVariable('second', cities)
        problem.addVariable('third', cities)
        
        # All cities must be different
        problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                            ['first', 'second', 'third'])
        
        # Flight constraints
        problem.addConstraint(lambda a, b: b in direct_flights[a], ['first', 'second'])
        problem.addConstraint(lambda b, c: c in direct_flights[b], ['second', 'third'])
        
        solutions = problem.getSolutions()
        
        if solutions:
            sol = solutions[0]
            sequence = [sol['first'], sol['second'], sol['third']]
            
            # Assign days
            current_day = 1
            itinerary = []
            
            for city in sequence:
                if city == 'Vilnius':
                    days = vilnius_days
                elif city == 'Munich':
                    days = munich_days
                else:  # Mykonos
                    days = mykonos_days
                
                end_day = current_day + days - 1
                itinerary.append({
                    "day_range": f"Day {current_day}-{end_day}",
                    "place": city
                })
                current_day = end_day + 1
    
    if itinerary:
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No valid itinerary found with given constraints"}))

if __name__ == "__main__":
    main()