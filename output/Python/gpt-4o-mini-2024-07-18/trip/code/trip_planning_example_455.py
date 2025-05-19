import json

def compute_itinerary():
    # Define the trip constraints
    days_total = 21
    stays = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    travel_days = {
        'Riga': ['Istanbul'],
        'Istanbul': ['Warsaw', 'Krakow'],
        'Warsaw': ['Reykjavik', 'Istanbul'],
        'Reykjavik': ['Warsaw'],
        'Krakow': ['Istanbul', 'Warsaw'],
    }
    
    itinerary = []
    current_day = 1

    # Visit Reykjavik
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Reykjavik"] - 1}', 'place': 'Reykjavik'})
    current_day += stays["Reykjavik"]

    # Meet friend in Riga between Day 1 and Day 2
    # Hence, we jump to Riga
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Riga'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Riga"] - 1}', 'place': 'Riga'})
    current_day += stays["Riga"]

    # Fly to Istanbul for wedding
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Riga', 'to': 'Istanbul'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Istanbul"] - 1}', 'place': 'Istanbul'})
    current_day += stays["Istanbul"]

    # Now travel to Warsaw
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Istanbul', 'to': 'Warsaw'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Warsaw"] - 1}', 'place': 'Warsaw'})
    current_day += stays["Warsaw"]

    # Finally, travel to Krakow
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Warsaw', 'to': 'Krakow'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stays["Krakow"] - 1}', 'place': 'Krakow'})
    current_day += stays["Krakow"]

    return itinerary

def main():
    itinerary = compute_itinerary()
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()