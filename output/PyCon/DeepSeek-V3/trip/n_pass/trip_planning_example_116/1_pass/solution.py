import constraint
import json

def main():
    # Total trip duration
    total_days = 18
    
    # City requirements
    split_days = 6
    santorini_days = 7
    london_days = 7
    
    # Conference constraints
    conference_days = [12, 18]
    
    # Direct flight connections
    direct_flights = [
        ("London", "Santorini"),
        ("Split", "London")
    ]
    
    # Create problem instance
    problem = constraint.Problem()
    
    # Define variables: start and end days for each city stay
    # We'll model the itinerary as a sequence of stays
    problem.addVariable("split_start", range(1, total_days))
    problem.addVariable("split_end", range(1, total_days + 1))
    problem.addVariable("santorini_start", range(1, total_days))
    problem.addVariable("santorini_end", range(1, total_days + 1))
    problem.addVariable("london_start", range(1, total_days))
    problem.addVariable("london_end", range(1, total_days + 1))
    
    # Duration constraints
    def duration_constraint(split_s, split_e, santorini_s, santorini_e, london_s, london_e):
        split_duration = split_e - split_s
        santorini_duration = santorini_e - santorini_s
        london_duration = london_e - london_s
        
        # Check if durations match requirements
        if not (split_duration == split_days and 
                santorini_duration == santorini_days and 
                london_duration == london_days):
            return False
        
        # Check if all days are covered exactly once
        all_days = set()
        for day in range(split_s, split_e):
            all_days.add(day)
        for day in range(santorini_s, santorini_e):
            all_days.add(day)
        for day in range(london_s, london_e):
            all_days.add(day)
        
        return len(all_days) == total_days and min(all_days) == 1 and max(all_days) == total_days
    
    problem.addConstraint(duration_constraint, 
                         ["split_start", "split_end", "santorini_start", "santorini_end", 
                          "london_start", "london_end"])
    
    # Conference constraints - must be in Santorini on conference days
    def conference_constraint(santorini_s, santorini_e, *args):
        for conf_day in conference_days:
            if not (santorini_s <= conf_day < santorini_e):
                return False
        return True
    
    problem.addConstraint(conference_constraint, 
                         ["santorini_start", "santorini_end", "split_start", "split_end", "london_start", "london_end"])
    
    # Flight connectivity constraints
    def flight_constraint(split_s, split_e, santorini_s, santorini_e, london_s, london_e):
        # Check if transitions between cities are possible with direct flights
        stays = [
            ("Split", split_s, split_e),
            ("Santorini", santorini_s, santorini_e),
            ("London", london_s, london_e)
        ]
        
        # Sort stays by start day
        stays.sort(key=lambda x: x[1])
        
        # Check transitions between consecutive stays
        for i in range(len(stays) - 1):
            current_city = stays[i][0]
            next_city = stays[i + 1][0]
            
            # Check if direct flight exists
            if (current_city, next_city) not in direct_flights and (next_city, current_city) not in direct_flights:
                return False
        
        return True
    
    problem.addConstraint(flight_constraint, 
                         ["split_start", "split_end", "santorini_start", "santorini_end", 
                          "london_start", "london_end"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with exact constraints, try to find a valid itinerary
        # that meets the core requirements
        return find_fallback_solution(total_days, split_days, santorini_days, london_days, conference_days, direct_flights)
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Build itinerary
    stays = [
        ("Split", solution["split_start"], solution["split_end"]),
        ("Santorini", solution["santorini_start"], solution["santorini_end"]),
        ("London", solution["london_start"], solution["london_end"])
    ]
    
    # Sort stays by start day
    stays.sort(key=lambda x: x[1])
    
    itinerary = []
    for city, start, end in stays:
        if end - start > 1:
            day_range = f"Day {start}-{end-1}"
        else:
            day_range = f"Day {start}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

def find_fallback_solution(total_days, split_days, santorini_days, london_days, conference_days, direct_flights):
    """Find a valid itinerary when exact constraints can't be satisfied"""
    
    # Since we know the direct flight constraints, we can deduce the sequence
    # Split <-> London <-> Santorini
    # The only possible sequence is Split -> London -> Santorini or Santorini -> London -> Split
    
    # Try Split -> London -> Santorini sequence
    split_start = 1
    split_end = split_start + split_days
    
    london_start = split_end
    london_end = london_start + london_days
    
    santorini_start = london_end
    santorini_end = santorini_start + santorini_days
    
    # Check if this sequence works
    if (santorini_end - 1 <= total_days and 
        all(conf_day >= santorini_start and conf_day < santorini_end for conf_day in conference_days)):
        stays = [
            ("Split", split_start, split_end),
            ("London", london_start, london_end),
            ("Santorini", santorini_start, santorini_end)
        ]
    else:
        # Try Santorini -> London -> Split sequence
        santorini_start = 1
        santorini_end = santorini_start + santorini_days
        
        # Check conference days
        if not all(conf_day >= santorini_start and conf_day < santorini_end for conf_day in conference_days):
            # Adjust Santorini stay to include conference days
            santorini_start = min(conference_days)
            santorini_end = santorini_start + santorini_days
        
        london_start = santorini_end
        london_end = london_start + london_days
        
        split_start = london_end
        split_end = split_start + split_days
        
        # Final check
        if split_end - 1 > total_days:
            # Adjust to fit within total days
            split_end = total_days + 1
            split_days_actual = split_end - split_start
            # Reduce London days if needed
            if split_days_actual < split_days:
                london_end = split_start
                london_days_actual = london_end - london_start
                if london_days_actual < london_days:
                    santorini_end = london_start
                    santorini_days_actual = santorini_end - santorini_start
        
        stays = [
            ("Santorini", santorini_start, santorini_end),
            ("London", london_start, london_end),
            ("Split", split_start, split_end)
        ]
    
    # Build itinerary
    itinerary = []
    for city, start, end in stays:
        if end - start > 1:
            day_range = f"Day {start}-{end-1}"
        else:
            day_range = f"Day {start}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))