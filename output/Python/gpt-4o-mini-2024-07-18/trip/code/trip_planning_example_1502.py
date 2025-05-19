import json

def create_trip_plan():
    # Initialize parameters
    total_days = 27
    itinerary = []
    
    # Set constraints based on the problem statement
    santorini_days = 3
    valencia_days = 4
    madrid_days = 2
    show_days = (6, 7)
    seville_days = 2
    bucharest_days = 3
    vienna_days = 4
    wedding_days = (3, 6)
    riga_days = 4
    conference_days = (20, 23)
    tallinn_days = 5
    workshop_days = (23, 27)
    krakow_days = 5
    friends_days = (11, 15)
    frankfurt_days = 4

    # Create a structured itinerary
    # Day 1 to Day 3: Vienna (Wedding)
    itinerary.append({'day_range': 'Day 1-3', 'place': 'Vienna'})
    
    # Day 4: Travel to Santorini
    itinerary.append({'flying': 'Day 4-4', 'from': 'Vienna', 'to': 'Santorini'})

    # Day 4 to Day 6: Santorini
    itinerary.append({'day_range': 'Day 4-6', 'place': 'Santorini'})

    # Day 7: Travel to Madrid
    itinerary.append({'flying': 'Day 7-7', 'from': 'Santorini', 'to': 'Madrid'})

    # Day 7 to Day 8: Madrid (Show from Day 6-7)
    itinerary.append({'day_range': 'Day 7-8', 'place': 'Madrid'})

    # Day 9: Travel to Valencia
    itinerary.append({'flying': 'Day 9-9', 'from': 'Madrid', 'to': 'Valencia'})

    # Day 9 to Day 12: Valencia
    itinerary.append({'day_range': 'Day 9-12', 'place': 'Valencia'})

    # Day 13: Travel to Seville
    itinerary.append({'flying': 'Day 13-13', 'from': 'Valencia', 'to': 'Seville'})

    # Day 13 to Day 14: Seville
    itinerary.append({'day_range': 'Day 13-14', 'place': 'Seville'})

    # Day 15: Travel to Madrid
    itinerary.append({'flying': 'Day 15-15', 'from': 'Seville', 'to': 'Madrid'})

    # Day 15 to Day 15: Madrid to Bucharest
    itinerary.append({'flying': 'Day 15-15', 'from': 'Madrid', 'to': 'Bucharest'})

    # Day 16 to Day 18: Bucharest
    itinerary.append({'day_range': 'Day 16-18', 'place': 'Bucharest'})

    # Day 19: Travel to Vienna
    itinerary.append({'flying': 'Day 19-19', 'from': 'Bucharest', 'to': 'Vienna'})

    # Day 19 to Day 22: Vienna
    itinerary.append({'day_range': 'Day 19-22', 'place': 'Vienna'})

    # Day 23: Travel to Riga
    itinerary.append({'flying': 'Day 23-23', 'from': 'Vienna', 'to': 'Riga'})

    # Day 23 to Day 26: Riga (Conference from Day 20-23)
    itinerary.append({'day_range': 'Day 23-26', 'place': 'Riga'})

    # Day 27: Travel to Tallinn
    itinerary.append({'flying': 'Day 27-27', 'from': 'Riga', 'to': 'Tallinn'})

    # Day 27 to Day 27: Tallinn (Workshop from Day 23-27)
    itinerary.append({'day_range': 'Day 27-27', 'place': 'Tallinn'})

    # Day 28: Travel to Krakow
    itinerary.append({'flying': 'Day 28-28', 'from': 'Tallinn', 'to': 'Krakow'})

    # Day 28 to Day 32: Krakow (Friends from Day 11-15)
    itinerary.append({'day_range': 'Day 28-32', 'place': 'Krakow'})

    # Day 33: Travel to Frankfurt
    itinerary.append({'flying': 'Day 33-33', 'from': 'Krakow', 'to': 'Frankfurt'})

    # Day 33 to Day 36: Frankfurt
    itinerary.append({'day_range': 'Day 33-36', 'place': 'Frankfurt'})

    # Convert to JSON format
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    trip_plan = create_trip_plan()
    print(trip_plan)