import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        "Mykonos": 4,
        "Nice": 3,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4
    }
    
    # Direct flights
    direct_flights = {
        "London": ["Copenhagen", "Mykonos", "Nice", "Oslo"],
        "Copenhagen": ["London", "Tallinn", "Nice", "Oslo"],
        "Tallinn": ["Copenhagen", "Oslo"],
        "Mykonos": ["London", "Nice"],
        "Oslo": ["Tallinn", "Nice", "London", "Copenhagen"],
        "Nice": ["Oslo", "London", "Mykonos", "Copenhagen"]
    }
    
    total_days = 16
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    for order in possible_orders:
        # Check flight connections
        valid_flights = True
        for i in range(len(order)-1):
            if order[i+1] not in direct_flights[order[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Nice must be last (days 14-16)
        if order[-1] != "Nice":
            continue
        
        # Try to assign days
        itinerary = []
        days_used = 0
        remaining_cities = order[:-1]  # all cities except Nice
        
        # First assign Oslo (must include at least one day between 10-14)
        if "Oslo" in remaining_cities:
            oslo_index = remaining_cities.index("Oslo")
            # Try to place Oslo to satisfy its constraint
            for possible_start in range(6, 11):  # Oslo can start between day 6-10 to include day 10-14
                oslo_end = possible_start + cities["Oslo"] - 1
                if oslo_end > 14:
                    continue  # Would overlap with Nice
                
                # Check if Oslo placement is valid
                if any(day in range(10, 15) for day in range(possible_start, oslo_end + 1)):
                    # Create temporary itinerary
                    temp_itinerary = []
                    temp_days_used = 0
                    temp_days = [False] * (total_days + 1)  # Track used days
                    
                    # Assign Oslo first
                    for day in range(possible_start, oslo_end + 1):
                        temp_days[day] = True
                    temp_itinerary.append({
                        "day_range": f"Day {possible_start}-{oslo_end}",
                        "place": "Oslo"
                    })
                    temp_days_used += cities["Oslo"]
                    
                    # Assign other cities
                    valid_assignment = True
                    for city in remaining_cities:
                        if city == "Oslo":
                            continue
                        
                        required_days = cities[city]
                        assigned = False
                        
                        # Find earliest available consecutive days
                        for start_day in range(1, total_days - required_days + 2):
                            end_day = start_day + required_days - 1
                            
                            # Check if days are available and don't overlap with Nice
                            if end_day >= 14:
                                continue
                            
                            days_available = True
                            for day in range(start_day, end_day + 1):
                                if temp_days[day]:
                                    days_available = False
                                    break
                            
                            if days_available:
                                for day in range(start_day, end_day + 1):
                                    temp_days[day] = True
                                temp_itinerary.append({
                                    "day_range": f"Day {start_day}-{end_day}",
                                    "place": city
                                })
                                temp_days_used += required_days
                                assigned = True
                                break
                        
                        if not assigned:
                            valid_assignment = False
                            break
                    
                    if valid_assignment and temp_days_used == 13:  # 13 days before Nice
                        # Add Nice (days 14-16)
                        temp_itinerary.append({
                            "day_range": "Day 14-16",
                            "place": "Nice"
                        })
                        # Sort by day range
                        temp_itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split(' ')[1]))
                        return {"itinerary": temp_itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))