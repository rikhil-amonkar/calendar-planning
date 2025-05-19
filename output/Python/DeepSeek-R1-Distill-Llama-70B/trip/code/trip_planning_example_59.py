import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Bucharest': 7,
            'Lyon': 7,
            'Porto': 4
        }
        self.fixed_stays = {
            'Bucharest': (7, 1, 7)
        }
        self.flights = {
            'Bucharest': ['Lyon'],
            'Lyon': ['Porto'],
            'Porto': []
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Bucharest'  # Start with Bucharest for the wedding

        # Bucharest stay
        bucharest_days = self.cities['Bucharest']
        itinerary.append({'day_range': f'Day 1-{bucharest_days}', 'place': 'Bucharest'})
        current_day += bucharest_days

        # Fly to Lyon
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Lyon'})
        current_day += 1

        # Lyon stay
        lyon_days = self.cities['Lyon']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + lyon_days - 1}', 'place': 'Lyon'})
        current_day += lyon_days

        # Fly to Porto
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Porto'})
        current_day += 1

        # Porto stay
        porto_days = self.cities['Porto']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + porto_days - 1}', 'place': 'Porto'})
        current_day += porto_days

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