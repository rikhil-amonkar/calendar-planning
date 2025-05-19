import json

def create_itinerary():
    itinerary = []
    days = 20
    day_count = 0

    # Day 1-5: Vienna (Meeting friend)
    itinerary.append({'day_range': 'Day 1-5', 'place': 'Vienna'})
    day_count += 5

    # Day 5: Travel to Prague
    itinerary.append({'flying': 'Day 5-5', 'from': 'Vienna', 'to': 'Prague'})
    
    # Day 5-9: Prague (Annual show)
    itinerary.append({'day_range': 'Day 5-9', 'place': 'Prague'})
    day_count += 4

    # Day 9: Travel to Split
    itinerary.append({'flying': 'Day 9-9', 'from': 'Prague', 'to': 'Split'})

    # Day 9-11: Split (Free time)
    itinerary.append({'day_range': 'Day 9-11', 'place': 'Split'})
    day_count += 2

    # Day 11-13: Split (Visiting relatives)
    itinerary.append({'day_range': 'Day 11-13', 'place': 'Split'})
    day_count += 2

    # Day 13: Travel to Munich
    itinerary.append({'flying': 'Day 13-13', 'from': 'Split', 'to': 'Munich'})
    
    # Day 13-15: Munich (Free time)
    itinerary.append({'day_range': 'Day 13-15', 'place': 'Munich'})
    day_count += 2

    # Day 15: Travel to Riga
    itinerary.append({'flying': 'Day 15-15', 'from': 'Munich', 'to': 'Riga'})

    # Day 15-16: Riga (Meeting friends)
    itinerary.append({'day_range': 'Day 15-16', 'place': 'Riga'})
    day_count += 1

    # Day 16: Travel to Stockholm
    itinerary.append({'flying': 'Day 16-16', 'from': 'Riga', 'to': 'Stockholm'})

    # Day 16-17: Stockholm (Conference)
    itinerary.append({'day_range': 'Day 16-17', 'place': 'Stockholm'})
    day_count += 1

    # Day 17: Travel to Brussels
    itinerary.append({'flying': 'Day 17-17', 'from': 'Stockholm', 'to': 'Brussels'})

    # Day 17-19: Brussels (Free time)
    itinerary.append({'day_range': 'Day 17-19', 'place': 'Brussels'})
    day_count += 2

    # Day 19: Travel to Amsterdam
    itinerary.append({'flying': 'Day 19-19', 'from': 'Brussels', 'to': 'Amsterdam'})

    # Day 19-22: Amsterdam (Free time)
    itinerary.append({'day_range': 'Day 19-21', 'place': 'Amsterdam'})
    day_count += 2

    # Day 21: Travel to Seville
    itinerary.append({'flying': 'Day 21-21', 'from': 'Amsterdam', 'to': 'Seville'})

    # Day 21-24: Seville (Free time)
    itinerary.append({'day_range': 'Day 21-24', 'place': 'Seville'})
    day_count += 3

    # Day 24: Travel to Istanbul
    itinerary.append({'flying': 'Day 24-24', 'from': 'Seville', 'to': 'Istanbul'})

    # Day 24-26: Istanbul (Free time)
    itinerary.append({'day_range': 'Day 24-26', 'place': 'Istanbul'})
    day_count += 2

    # Day 26: Travel back to Vienna
    itinerary.append({'flying': 'Day 26-26', 'from': 'Istanbul', 'to': 'Vienna'})

    # Finalizing itinerary
    json_output = json.dumps(itinerary, indent=4)
    return json_output

if __name__ == "__main__":
    print(create_itinerary())