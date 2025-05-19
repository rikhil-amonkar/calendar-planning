import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Edinburgh': 5,
            'Stockholm': 2,
            'Budapest': 5,
            'Munich': 3,
            'Krakow': 4,
            'Barcelona': 5,
            'Warsaw': 5,
            'Riga': 5,
            'Bucharest': 2,
            'Vienna': 5
        }
        self.fixed_stays = {
            'Edinburgh': (5, 1, 5),
            'Stockholm': (2, 17, 18),
            'Budapest': (5, 9, 13),
            'Munich': (3, 18, 20),
            'Warsaw': (5, 25, 29)
        }
        self.flights = {
            'Edinburgh': ['Stockholm', 'Krakow', 'Munich', 'Barcelona', 'Budapest'],
            'Stockholm': ['Krakow', 'Munich', 'Budapest', 'Barcelona', 'Edinburgh', 'Riga', 'Warsaw'],
            'Budapest': ['Munich', 'Krakow', 'Warsaw', 'Barcelona', 'Vienna', 'Bucharest'],
            'Munich': ['Krakow', 'Warsaw', 'Bucharest', 'Edinburgh', 'Barcelona', 'Budapest'],
            'Krakow': ['Warsaw', 'Munich', 'Budapest', 'Barcelona', 'Edinburgh', 'Stockholm'],
            'Barcelona': ['Warsaw', 'Munich', 'Krakow', 'Budapest', 'Edinburgh', 'Stockholm', 'Riga', 'Bucharest'],
            'Warsaw': ['Krakow', 'Munich', 'Budapest', 'Barcelona', 'Edinburgh', 'Stockholm', 'Riga'],
            'Riga': ['Munich', 'Warsaw', 'Bucharest', 'Barcelona', 'Edinburgh', 'Stockholm'],
            'Bucharest': ['Warsaw', 'Munich', 'Krakow', 'Barcelona', 'Budapest', 'Edinburgh'],
            'Vienna': ['Riga', 'Bucharest', 'Warsaw', 'Munich', 'Krakow', 'Barcelona', 'Budapest']
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Edinburgh'  # Start with Edinburgh as per the fixed stay

        # Edinburgh stay
        edinburgh_days = self.cities['Edinburgh']
        itinerary.append({'day_range': f'Day 1-{edinburgh_days}', 'place': 'Edinburgh'})
        current_day += edinburgh_days

        # Fly to Stockholm
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Edinburgh', 'to': 'Stockholm'})
        current_day += 1

        # Stockholm stay
        stockholm_days = self.cities['Stockholm']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + stockholm_days - 1}', 'place': 'Stockholm'})
        current_day += stockholm_days

        # Fly to Budapest
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stockholm', 'to': 'Budapest'})
        current_day += 1

        # Budapest stay
        budapest_days = self.cities['Budapest']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + budapest_days - 1}', 'place': 'Budapest'})
        current_day += budapest_days

        # Fly to Munich
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Budapest', 'to': 'Munich'})
        current_day += 1

        # Munich stay
        munich_days = self.cities['Munich']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + munich_days - 1}', 'place': 'Munich'})
        current_day += munich_days

        # Fly to Krakow
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Munich', 'to': 'Krakow'})
        current_day += 1

        # Krakow stay
        krakow_days = self.cities['Krakow']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + krakow_days - 1}', 'place': 'Krakow'})
        current_day += krakow_days

        # Fly to Warsaw
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Warsaw'})
        current_day += 1

        # Warsaw stay
        warsaw_days = self.cities['Warsaw']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + warsaw_days - 1}', 'place': 'Warsaw'})
        current_day += warsaw_days

        # Fly to Riga
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Warsaw', 'to': 'Riga'})
        current_day += 1

        # Riga stay
        riga_days = self.cities['Riga']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + riga_days - 1}', 'place': 'Riga'})
        current_day += riga_days

        # Fly to Bucharest
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Riga', 'to': 'Bucharest'})
        current_day += 1

        # Bucharest stay
        bucharest_days = self.cities['Bucharest']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + bucharest_days - 1}', 'place': 'Bucharest'})
        current_day += bucharest_days

        # Fly to Vienna
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Vienna'})
        current_day += 1

        # Vienna stay
        vienna_days = self.cities['Vienna']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + vienna_days - 1}', 'place': 'Vienna'})
        current_day += vienna_days

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