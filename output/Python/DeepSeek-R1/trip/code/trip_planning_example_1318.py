import json

def main():
    cities = {
        'Oslo': {'days': 2, 'constraint': (24, 25)},
        'Helsinki': {'days': 2},
        'Edinburgh': {'days': 3},
        'Riga': {'days': 2},
        'Tallinn': {'days': 5, 'constraint': (4, 8)},
        'Budapest': {'days': 5},
        'Vilnius': {'days': 5},
        'Porto': {'days': 5},
        'Geneva': {'days': 4}
    }

    flights = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Edinburgh': ['Porto', 'Budapest', 'Geneva', 'Oslo', 'Helsinki', 'Riga'],
        'Riga': ['Tallinn', 'Oslo', 'Helsinki', 'Vilnius'],
        'Vilnius': ['Helsinki', 'Oslo'],
        'Tallinn': ['Vilnius', 'Helsinki', 'Oslo'],
        'Helsinki': ['Vilnius', 'Budapest', 'Oslo', 'Geneva', 'Tallinn'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Geneva': ['Edinburgh', 'Budapest', 'Helsinki', 'Oslo', 'Porto'],
        'Oslo': ['Porto', 'Edinburgh', 'Geneva', 'Helsinki', 'Vilnius', 'Budapest', 'Riga', 'Tallinn']
    }

    itinerary = []
    current_day = 1

    # Edinburgh first
    edinburgh_days = cities['Edinburgh']['days']
    itinerary.append({'day_range': f'Day {current_day}-{current_day + edinburgh_days - 1}', 'place': 'Edinburgh'})
    current_day += edinburgh_days  # Day 4

    # Fly to Riga
    riga_days = cities['Riga']['days']
    itinerary.append({'day_range': f'Day {current_day}-{current_day + riga_days - 1}', 'place': 'Riga'})
    current_day += riga_days  # Day 6

    # Fly to Tallinn (must start by day 4)
    # Adjust to meet Tallinn's constraint
    tallinn_start = 4
    if current_day > tallinn_start:
        current_day = tallinn_start
    itinerary.append({'day_range': f'Day {tallinn_start}-{tallinn_start + cities["Tallinn"]["days"] - 1}', 'place': 'Tallinn'})
    current_day = tallinn_start + cities["Tallinn"]["days"]  # Day 9

    # Fly to Vilnius
    vilnius_days = cities['Vilnius']['days']
    itinerary.append({'day_range': f'Day {current_day}-{current_day + vilnius_days - 1}', 'place': 'Vilnius'})
    current_day += vilnius_days  # Day 14

    # Fly to Helsinki
    helsinki_days = cities['Helsinki']['days']
    itinerary.append({'day_range': f'Day {current_day}-{current_day + helsinki_days - 1}', 'place': 'Helsinki'})
    current_day += helsinki_days  # Day 16

    # Fly to Budapest
    budapest_days = cities['Budapest']['days']
    itinerary.append({'day_range': f'Day {current_day}-{current_day + budapest_days - 1}', 'place': 'Budapest'})
    current_day += budapest_days  # Day 21

    # Fly to Geneva
    geneva_days = cities['Geneva']['days']
    itinerary.append({'day_range': f'Day {current_day}-{current_day + geneva_days - 1}', 'place': 'Geneva'})
    current_day += geneva_days  # Day 25

    # Fly to Oslo
    oslo_start = 24
    oslo_end = 25
    itinerary.append({'day_range': f'Day {oslo_start}-{oslo_end}', 'place': 'Oslo'})

    # Check if total days exceed 25
    total_days = 0
    for entry in itinerary:
        start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
        total_days += end - start + 1

    if total_days != 25:
        adjust = 25 - total_days
        if adjust != 0:
            # Adjust Geneva days
            geneva_entry = next(e for e in itinerary if e['place'] == 'Geneva')
            start, end = map(int, geneva_entry['day_range'].split(' ')[1].split('-'))
            new_end = end + adjust
            geneva_entry['day_range'] = f'Day {start}-{new_end}'
            current_day += adjust

            # Adjust Oslo
            oslo_entry = next(e for e in itinerary if e['place'] == 'Oslo')
            oslo_entry['day_range'] = f'Day {new_end + 1}-{new_end + 2}'

    output = {'itinerary': itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()