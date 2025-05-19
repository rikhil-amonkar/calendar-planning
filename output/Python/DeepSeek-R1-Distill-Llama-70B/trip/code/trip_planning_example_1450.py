import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
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
        self.fixed_stays = {
            'Krakow': (5, 5, 9),
            'Istanbul': (5, 25, 29)
        }
        self.flights = {
            'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Munich', 'Stockholm'],
            'Frankfurt': ['Istanbul', 'Oslo', 'Munich', 'Hamburg', 'Florence', 'Stockholm'],
            'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence'],
            'Hamburg': ['Stockholm', 'Oslo', 'Istanbul', 'Frankfurt'],
            'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Munich', 'Hamburg', 'Frankfurt'],
            'Stockholm': ['Oslo', 'Hamburg', 'Munich', 'Krakow', 'Frankfurt'],
            'Vilnius': ['Istanbul', 'Frankfurt', 'Munich'],
            'Istanbul': ['Stockholm', 'Oslo', 'Hamburg', 'Frankfurt', 'Munich'],
            'Florence': ['Munich'],
            'Santorini': ['Oslo']
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Krakow'  # Start with Krakow to attend the workshop

        # Krakow stay
        krakow_days = self.cities['Krakow']
        itinerary.append({'day_range': f'Day 1-{krakow_days}', 'place': 'Krakow'})
        current_day += krakow_days

        # Fly to Frankfurt
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Frankfurt'})
        current_day += 1

        # Frankfurt stay
        frankfurt_days = self.cities['Frankfurt']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + frankfurt_days - 1}', 'place': 'Frankfurt'})
        current_day += frankfurt_days

        # Fly to Hamburg
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Frankfurt', 'to': 'Hamburg'})
        current_day += 1

        # Hamburg stay
        hamburg_days = self.cities['Hamburg']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + hamburg_days - 1}', 'place': 'Hamburg'})
        current_day += hamburg_days

        # Fly to Oslo
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Hamburg', 'to': 'Oslo'})
        current_day += 1

        # Oslo stay
        oslo_days = self.cities['Oslo']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + oslo_days - 1}', 'place': 'Oslo'})
        current_day += oslo_days

        # Fly to Stockholm
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Stockholm'})
        current_day += 1

        # Stockholm stay
        stockholm_days = self.cities['Stockholm']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + stockholm_days - 1}', 'place': 'Stockholm'})
        current_day += stockholm_days

        # Fly to Munich
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stockholm', 'to': 'Munich'})
        current_day += 1

        # Munich stay
        munich_days = self.cities['Munich']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + munich_days - 1}', 'place': 'Munich'})
        current_day += munich_days

        # Fly to Florence
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Munich', 'to': 'Florence'})
        current_day += 1

        # Florence stay
        florence_days = self.cities['Florence']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + florence_days - 1}', 'place': 'Florence'})
        current_day += florence_days

        # Fly to Santorini
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Florence', 'to': 'Santorini'})
        current_day += 1

        # Santorini stay
        santorini_days = self.cities['Santorini']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + santorini_days - 1}', 'place': 'Santorini'})
        current_day += santorini_days

        # Fly to Istanbul
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Santorini', 'to': 'Istanbul'})
        current_day += 1

        # Istanbul stay
        istanbul_days = self.cities['Istanbul']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + istanbul_days - 1}', 'place': 'Istanbul'})
        current_day += istanbul_days

        return itinerary

planner = TripPlanner()
itinerary = planner.compute_itinerary()

# Adjusting the day ranges to match the required format
for item in itinerary:
    if 'day_range' in item:
        days = item['day_range'].split('-')
        start_day = days[1]
        end_day = days[2] if len(days) > 2 else start_day
        item['day_range'] = f'Day {start_day}-{end_day}'
    elif 'flying' in item:
        flying_day = item['flying'].split('-')[1]
        item['flying'] = f'Day {flying_day}'

print(json.dumps(itinerary, indent=2))