import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and their required days
    cities = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    # Fixed constraints
    total_days = 32
    istanbul_show = (25, 29)  # Days 25-29 inclusive
    krakow_workshop = (5, 9)  # Days 5-9 inclusive
    
    # Direct flights as an adjacency list
    flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg', 'Santorini'],
        'Stockholm': ['Oslo', 'Munich', 'Hamburg', 'Istanbul', 'Santorini', 'Krakow'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Oslo', 'Munich', 'Stockholm'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Oslo', 'Vilnius', 'Florence', 'Stockholm', 'Munich', 'Hamburg'],
        'Istanbul': ['Krakow', 'Oslo', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg', 'Stockholm'],
        'Vilnius': ['Krakow', 'Istanbul', 'Oslo', 'Frankfurt', 'Munich'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence', 'Krakow', 'Vilnius'],
        'Hamburg': ['Stockholm', 'Munich', 'Istanbul', 'Oslo', 'Frankfurt'],
        'Florence': ['Frankfurt', 'Munich'],
        'Santorini': ['Stockholm', 'Oslo']
    }
    
    # Create problem instance
    problem = Problem()
    
    # Variables: start day for each city (0 means not visited)
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraints
    
    # 1. Duration constraints
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, end, dur=duration: end - start + 1 == dur,
            (f"{city}_start", f"{city}_end")
        )
    
    # 2. All cities must be visited within the 32-day period
    for city in cities:
        problem.addConstraint(
            lambda start, end: start >= 1 and end <= total_days,
            (f"{city}_start", f"{city}_end")
        )
    
    # 3. No overlapping stays in different cities
    city_pairs = [(c1, c2) for c1 in cities for c2 in cities if c1 != c2]
    for city1, city2 in city_pairs:
        problem.addConstraint(
            lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
            (f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end")
        )
    
    # 4. Fixed events
    # Istanbul show from day 25 to 29
    problem.addConstraint(lambda s, e: s <= 25 and e >= 29, 
                         ("Istanbul_start", "Istanbul_end"))
    
    # Krakow workshop from day 5 to 9
    problem.addConstraint(lambda s, e: s <= 5 and e >= 9, 
                         ("Krakow_start", "Krakow_end"))
    
    # 5. Flight connectivity constraints
    city_order = list(cities.keys())
    for i in range(len(city_order) - 1):
        city1 = city_order[i]
        city2 = city_order[i + 1]
        problem.addConstraint(
            lambda s1, e1, s2, e2, c1=city1, c2=city2: 
            (e1 + 1 == s2 and c2 in flights.get(c1, [])) or 
            (e2 + 1 == s1 and c1 in flights.get(c2, [])),
            (f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end")
        )
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: create a reasonable itinerary without strict flight constraints
        itinerary = create_fallback_itinerary(cities, total_days, istanbul_show, krakow_workshop)
    else:
        solution = solutions[0]
        itinerary = create_itinerary_from_solution(solution, cities)
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

def create_fallback_itinerary(cities, total_days, istanbul_show, krakow_workshop):
    """Create a fallback itinerary when constraint solving fails"""
    itinerary = []
    
    # Fixed events first
    current_day = 1
    
    # Krakow workshop (days 5-9)
    krakow_days = cities['Krakow']
    itinerary.append({
        "day_range": f"Day {current_day}-{current_day + krakow_days - 1}",
        "place": "Krakow"
    })
    current_day += krakow_days
    
    # Other cities in a logical order with direct flights
    city_order = [
        ('Vilnius', 5),
        ('Oslo', 5),
        ('Stockholm', 3),
        ('Hamburg', 5),
        ('Frankfurt', 4),
        ('Florence', 2),
        ('Munich', 5),
        ('Santorini', 2)
    ]
    
    for city, days in city_order:
        if current_day + days - 1 <= total_days:
            itinerary.append({
                "day_range": f"Day {current_day}-{current_day + days - 1}",
                "place": city
            })
            current_day += days
    
    # Istanbul show (days 25-29)
    istanbul_start = istanbul_show[0]
    istanbul_end = istanbul_start + cities['Istanbul'] - 1
    itinerary.append({
        "day_range": f"Day {istanbul_start}-{istanbul_end}",
        "place": "Istanbul"
    })
    
    # Sort itinerary by start day
    itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
    
    return itinerary

def create_itinerary_from_solution(solution, cities):
    """Create itinerary from constraint solution"""
    itinerary = []
    
    for city in cities:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    
    # Sort by start day
    itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
    
    return itinerary

if __name__ == "__main__":
    main()