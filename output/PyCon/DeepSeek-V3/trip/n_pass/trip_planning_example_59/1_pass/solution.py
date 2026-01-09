import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Lyon', 'Bucharest', 'Porto']
    required_days = {
        'Lyon': 7,
        'Bucharest': 7,
        'Porto': 4
    }
    
    total_days = 16
    
    # Define variables for start days of each city visit
    # We'll model this as three consecutive visits with start days
    problem.addVariable('start_Lyon', range(1, total_days + 1))
    problem.addVariable('start_Bucharest', range(1, total_days + 1))
    problem.addVariable('start_Porto', range(1, total_days + 1))
    
    # Add constraint that all start days must be different
    problem.addConstraint(AllDifferentConstraint(), ['start_Lyon', 'start_Bucharest', 'start_Porto'])
    
    # Constraint: Total days must be exactly 16
    def total_days_constraint(lyon_start, bucharest_start, porto_start):
        # Calculate end days for each city
        lyon_end = lyon_start + required_days['Lyon'] - 1
        bucharest_end = bucharest_start + required_days['Bucharest'] - 1
        porto_end = porto_start + required_days['Porto'] - 1
        
        # All visits must be within the 16-day range
        if (lyon_end > total_days or bucharest_end > total_days or porto_end > total_days):
            return False
        
        # Check for overlaps - visits cannot overlap
        visits = [
            (lyon_start, lyon_end, 'Lyon'),
            (bucharest_start, bucharest_end, 'Bucharest'),
            (porto_start, porto_end, 'Porto')
        ]
        
        # Sort by start day
        visits.sort()
        
        # Check if visits are consecutive without overlaps
        for i in range(len(visits) - 1):
            if visits[i][1] >= visits[i + 1][0]:
                return False
        
        return True
    
    problem.addConstraint(total_days_constraint, 
                         ['start_Lyon', 'start_Bucharest', 'start_Porto'])
    
    # Constraint: Wedding in Bucharest between day 1 and 7
    def wedding_constraint(bucharest_start):
        bucharest_end = bucharest_start + required_days['Bucharest'] - 1
        # Bucharest visit must include at least one day between 1 and 7
        return bucharest_start <= 7 and bucharest_end >= 1
    
    problem.addConstraint(wedding_constraint, ['start_Bucharest'])
    
    # Constraint: Direct flights only (Bucharest-Lyon, Lyon-Porto)
    # This means the itinerary must have Bucharest and Lyon adjacent, and Lyon and Porto adjacent
    def flight_constraint(lyon_start, bucharest_start, porto_start):
        visits = [
            (lyon_start, 'Lyon'),
            (bucharest_start, 'Bucharest'),
            (porto_start, 'Porto')
        ]
        
        # Sort by start day
        visits.sort()
        
        # Check if adjacent cities have direct flights
        order = [visit[1] for visit in visits]
        
        # Check if Lyon is between Bucharest and Porto
        lyon_index = order.index('Lyon')
        if lyon_index == 0:
            return order[1] == 'Bucharest' or order[1] == 'Porto'
        elif lyon_index == 2:
            return order[1] == 'Bucharest' or order[1] == 'Porto'
        else:  # Lyon in middle
            return (order[0] == 'Bucharest' and order[2] == 'Porto') or \
                   (order[0] == 'Porto' and order[2] == 'Bucharest')
    
    problem.addConstraint(flight_constraint, 
                         ['start_Lyon', 'start_Bucharest', 'start_Porto'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create the itinerary in chronological order
    visits = [
        (solution['start_Lyon'], solution['start_Lyon'] + required_days['Lyon'] - 1, 'Lyon'),
        (solution['start_Bucharest'], solution['start_Bucharest'] + required_days['Bucharest'] - 1, 'Bucharest'),
        (solution['start_Porto'], solution['start_Porto'] + required_days['Porto'] - 1, 'Porto')
    ]
    
    # Sort by start day
    visits.sort()
    
    # Format the itinerary
    itinerary = []
    for start, end, city in visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))