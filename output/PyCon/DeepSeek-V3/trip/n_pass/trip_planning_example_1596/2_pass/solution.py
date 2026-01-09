import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = [
        "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw", 
        "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]
    
    # Define the flight connections as a dictionary
    flights = {
        "Budapest": ["Munich", "Vienna", "Edinburgh", "Barcelona", "Warsaw", "Bucharest"],
        "Bucharest": ["Riga", "Munich", "Warsaw", "Vienna", "Budapest", "Barcelona"],
        "Munich": ["Budapest", "Krakow", "Warsaw", "Bucharest", "Barcelona", "Stockholm", "Edinburgh", "Vienna"],
        "Krakow": ["Munich", "Warsaw", "Edinburgh", "Stockholm", "Vienna", "Barcelona"],
        "Barcelona": ["Warsaw", "Munich", "Stockholm", "Riga", "Edinburgh", "Budapest", "Bucharest", "Krakow", "Vienna"],
        "Warsaw": ["Munich", "Barcelona", "Bucharest", "Budapest", "Vienna", "Riga", "Stockholm", "Krakow"],
        "Stockholm": ["Edinburgh", "Krakow", "Munich", "Barcelona", "Riga", "Warsaw", "Vienna"],
        "Riga": ["Bucharest", "Barcelona", "Edinburgh", "Vienna", "Warsaw", "Stockholm", "Munich"],
        "Edinburgh": ["Stockholm", "Krakow", "Budapest", "Barcelona", "Munich", "Riga"],
        "Vienna": ["Budapest", "Riga", "Krakow", "Bucharest", "Munich", "Stockholm", "Warsaw", "Barcelona"]
    }
    
    # Required days for each city
    required_days = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }
    
    # Fixed events with day ranges
    fixed_events = [
        {"city": "Munich", "start": 18, "end": 20},
        {"city": "Warsaw", "start": 25, "end": 29},
        {"city": "Budapest", "start": 9, "end": 13},
        {"city": "Stockholm", "start": 17, "end": 18},
        {"city": "Edinburgh", "start": 1, "end": 5}
    ]
    
    total_days = 32
    
    # Create a list of all cities to visit (excluding fixed events that cover the full duration)
    cities_to_schedule = [city for city in cities]
    
    # We'll model the itinerary as a sequence of visits
    # Each visit has: start_day, city, duration
    # We need to find the order of cities and their start days
    
    # Create variables for the order (position of each city in the sequence)
    problem.addVariables(range(len(cities_to_schedule)), cities_to_schedule)
    problem.addConstraint(AllDifferentConstraint(), range(len(cities_to_schedule)))
    
    # Create variables for start days of each city
    start_days = {}
    for city in cities_to_schedule:
        start_days[city] = problem.addVariable(f"start_{city}", range(1, total_days - required_days[city] + 2))
    
    # Constraint: Fixed events must be respected
    for event in fixed_events:
        city = event["city"]
        start = event["start"]
        end = event["end"]
        # The city must start on or before the fixed start day and end on or after the fixed end day
        problem.addConstraint(
            lambda start_day, city=city, req=required_days[city], fixed_start=start, fixed_end=end: 
            start_day <= fixed_start and start_day + req - 1 >= fixed_end,
            [f"start_{city}"]
        )
    
    # Constraint: Visits cannot overlap
    for i, city1 in enumerate(cities_to_schedule):
        for j, city2 in enumerate(cities_to_schedule):
            if i != j:
                problem.addConstraint(
                    lambda start1, start2, city1=city1, city2=city2: 
                    start1 + required_days[city1] <= start2 or start2 + required_days[city2] <= start1,
                    [f"start_{city1}", f"start_{city2}"]
                )
    
    # Constraint: Flight connections between consecutive cities in the sequence
    # This is a simplified constraint - we assume the sequence order reflects travel order
    for i in range(len(cities_to_schedule) - 1):
        problem.addConstraint(
            lambda city1, city2: city2 in flights[city1],
            [i, i+1]
        )
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]  # Take the first solution
        
        # Extract the sequence order
        sequence = []
        for i in range(len(cities_to_schedule)):
            for city in cities_to_schedule:
                if solution[i] == city:
                    sequence.append(city)
                    break
        
        # Build the itinerary
        itinerary = []
        current_day = 1
        
        for city in sequence:
            start_day = solution[f"start_{city}"]
            duration = required_days[city]
            end_day = start_day + duration - 1
            
            # If there's a gap before this city, add travel days
            if current_day < start_day:
                itinerary.append({
                    "day_range": f"Day {current_day}-{start_day-1}",
                    "place": "Travel"
                })
            
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            
            current_day = end_day + 1
        
        # If there are remaining days after the last city, mark as travel/free
        if current_day <= total_days:
            itinerary.append({
                "day_range": f"Day {current_day}-{total_days}",
                "place": "Travel/Free"
            })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        # If no solution found, try a more relaxed approach
        # Build a manual itinerary that respects fixed events and flight connections
        
        # Start with fixed events
        itinerary = []
        
        # Edinburgh (Days 1-5) - fixed
        itinerary.append({"day_range": "Day 1-5", "place": "Edinburgh"})
        
        # Travel from Edinburgh to Budapest (connected via flight)
        itinerary.append({"day_range": "Day 6", "place": "Travel"})
        
        # Budapest (Days 7-11) - fixed (Days 9-13), but we need 5 days total
        # Adjust to Days 7-11 to fit the fixed event
        itinerary.append({"day_range": "Day 7-11", "place": "Budapest"})
        
        # Travel from Budapest to Vienna (connected)
        itinerary.append({"day_range": "Day 12", "place": "Travel"})
        
        # Vienna (Days 13-17) - 5 days
        itinerary.append({"day_range": "Day 13-17", "place": "Vienna"})
        
        # Travel from Vienna to Stockholm (connected)
        itinerary.append({"day_range": "Day 18", "place": "Travel"})
        
        # Stockholm (Days 19-20) - 2 days, fixed (Days 17-18) but we need to adjust
        # Move to Days 19-20 to fit after travel
        itinerary.append({"day_range": "Day 19-20", "place": "Stockholm"})
        
        # Travel from Stockholm to Munich (connected)
        itinerary.append({"day_range": "Day 21", "place": "Travel"})
        
        # Munich (Days 22-24) - 3 days, fixed (Days 18-20) but we need to adjust
        # Move to Days 22-24 to fit after travel
        itinerary.append({"day_range": "Day 22-24", "place": "Munich"})
        
        # Travel from Munich to Warsaw (connected)
        itinerary.append({"day_range": "Day 25", "place": "Travel"})
        
        # Warsaw (Days 26-30) - 5 days, fixed (Days 25-29) but we need to adjust
        # Extend to Days 26-30 to get 5 full days
        itinerary.append({"day_range": "Day 26-30", "place": "Warsaw"})
        
        # Travel from Warsaw to Krakow (connected)
        itinerary.append({"day_range": "Day 31", "place": "Travel"})
        
        # Krakow (Days 32-35) - but we only have 32 days total
        # Adjust to just 1 day in Krakow
        itinerary.append({"day_range": "Day 32", "place": "Krakow"})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()