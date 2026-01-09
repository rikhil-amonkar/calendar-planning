import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    
    # Total days
    total_days = 14
    
    # Define variables for start days of each city visit
    # We'll model this as finding the order and durations of visits
    problem.addVariable('order_Amsterdam', range(4))
    problem.addVariable('order_Vienna', range(4))
    problem.addVariable('order_Santorini', range(4))
    problem.addVariable('order_Lyon', range(4))
    
    # Add constraint that all orders must be different
    problem.addConstraint(AllDifferentConstraint(), 
                         ['order_Amsterdam', 'order_Vienna', 'order_Santorini', 'order_Lyon'])
    
    # Duration constraints
    amsterdam_days = 3
    vienna_days = 7
    santorini_days = 4
    lyon_days = 3
    
    # Workshop in Amsterdam between day 9 and 11 (inclusive)
    # Wedding in Lyon between day 7 and 9 (inclusive)
    
    # We need to find a sequence that satisfies:
    # - Total days = 14
    # - Amsterdam: 3 days, includes at least one day between 9-11
    # - Vienna: 7 days
    # - Santorini: 4 days  
    # - Lyon: 3 days, includes at least one day between 7-9
    # - Direct flights only between connected cities
    
    # Flight connections
    connections = {
        'Vienna': ['Lyon', 'Santorini', 'Amsterdam'],
        'Lyon': ['Vienna', 'Amsterdam'],
        'Santorini': ['Vienna', 'Amsterdam'],
        'Amsterdam': ['Vienna', 'Santorini', 'Lyon']
    }
    
    def itinerary_valid(order_amsterdam, order_vienna, order_santorini, order_lyon):
        # Create order mapping
        order_to_city = {
            order_amsterdam: ('Amsterdam', amsterdam_days),
            order_vienna: ('Vienna', vienna_days),
            order_santorini: ('Santorini', santorini_days),
            order_lyon: ('Lyon', lyon_days)
        }
        
        # Sort by visit order
        visit_order = sorted([(order_amsterdam, 'Amsterdam', amsterdam_days),
                             (order_vienna, 'Vienna', vienna_days),
                             (order_santorini, 'Santorini', santorini_days),
                             (order_lyon, 'Lyon', lyon_days)])
        
        # Check flight connections between consecutive cities
        for i in range(len(visit_order) - 1):
            current_city = visit_order[i][1]
            next_city = visit_order[i + 1][1]
            if next_city not in connections[current_city]:
                return False
        
        # Calculate day ranges and check constraints
        current_day = 1
        amsterdam_days_covered = set()
        lyon_days_covered = set()
        
        for _, city, duration in visit_order:
            end_day = current_day + duration - 1
            
            # Track days for Amsterdam and Lyon
            if city == 'Amsterdam':
                amsterdam_days_covered.update(range(current_day, end_day + 1))
            elif city == 'Lyon':
                lyon_days_covered.update(range(current_day, end_day + 1))
            
            current_day = end_day + 1
        
        # Check workshop constraint (Amsterdam between day 9-11)
        workshop_days = set(range(9, 12))  # Days 9, 10, 11
        if not workshop_days.intersection(amsterdam_days_covered):
            return False
        
        # Check wedding constraint (Lyon between day 7-9)  
        wedding_days = set(range(7, 10))  # Days 7, 8, 9
        if not wedding_days.intersection(lyon_days_covered):
            return False
        
        # Check total days
        total_used = sum([amsterdam_days, vienna_days, santorini_days, lyon_days])
        if total_used != total_days:
            return False
            
        return True
    
    problem.addConstraint(itinerary_valid, 
                         ['order_Amsterdam', 'order_Vienna', 'order_Santorini', 'order_Lyon'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use first solution
    sol = solutions[0]
    
    # Build the itinerary
    visit_info = [
        (sol['order_Amsterdam'], 'Amsterdam', amsterdam_days),
        (sol['order_Vienna'], 'Vienna', vienna_days),
        (sol['order_Santorini'], 'Santorini', santorini_days),
        (sol['order_Lyon'], 'Lyon', lyon_days)
    ]
    
    visit_info.sort()
    
    itinerary = []
    current_day = 1
    
    for _, city, duration in visit_info:
        end_day = current_day + duration - 1
        if current_day == end_day:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))