import json

def calculate_itinerary():
    # Trip parameters
    total_days = 15
    city_days = {
        'Paris': 6,
        'Madrid': 7,
        'Bucharest': 2,
        'Seville': 3
    }
    
    # Flight connections (direct flights)
    flights = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Bucharest': ['Paris', 'Madrid'],
        'Madrid': ['Paris', 'Bucharest', 'Seville'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Itinerary plan
    itinerary = []
    
    current_day = 1
    
    # 1. Stay in Paris for 6 days
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_days["Paris"] - 1}', 'place': 'Paris'})
    current_day += city_days["Paris"]
    
    # 2. Fly to Madrid and stay for 7 days (including annual show days)
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Paris', 'to': 'Madrid'})
    current_day += 1
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_days["Madrid"] - 1}', 'place': 'Madrid'})
    current_day += city_days["Madrid"]
    
    # 3. Fly to Bucharest for 2 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Madrid', 'to': 'Bucharest'})
    current_day += 1
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_days["Bucharest"] - 1}', 'place': 'Bucharest'})
    current_day += city_days["Bucharest"]
    
    # 4. Fly to Seville for 3 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Seville'})
    current_day += 1
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_days["Seville"] - 1}', 'place': 'Seville'})
    current_day += city_days["Seville"]
    
    # 5. Return to Bucharest to visit relatives for 2 days
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Seville', 'to': 'Bucharest'})
    current_day += 1
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Bucharest'})
    
    # Convert to JSON format
    output = json.dumps(itinerary, indent=4)
    
    return output

# Execute itinerary calculation
if __name__ == "__main__":
    print(calculate_itinerary())