import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Nice': 5,
            'Krakow': 6,
            'Dublin': 7,
            'Lyon': 4,
            'Frankfurt': 2
        }
        self.flights = {
            'Nice': ['Dublin', 'Frankfurt', 'Lyon'],
            'Krakow': ['Frankfurt'],
            'Dublin': ['Frankfurt', 'Krakow', 'Lyon'],
            'Lyon': ['Frankfurt', 'Dublin'],
            'Frankfurt': ['Krakow', 'Lyon', 'Dublin', 'Nice']
        }
        self.itinerary = []
        self.current_day = 1
        self.current_city = 'Nice'

    def plan_trip(self):
        self.stay('Nice', 5)
        self.visit_next_city()
        return self.itinerary

    def visit_next_city(self):
        while self.current_day <= 20:
            next_cities = self.flights[self.current_city]
            for city in next_cities:
                if city in self.cities and self.cities[city] > 0:
                    self.fly_to(city)
                    self.stay(city, self.cities[city])
                    self.visit_next_city()
                    break
            else:
                break

    def stay(self, city, days):
        self.itinerary.append({'day_range': f'Day {self.current_day}-{self.current_day + days - 1}', 'place': city})
        self.current_day += days
        self.cities[city] = 0

    def fly_to(self, city):
        self.itinerary.append({'flying': f'Day {self.current_day - 1}-{self.current_day - 1}', 'from': self.current_city, 'to': city})
        self.current_city = city

planner = TripPlanner()
itinerary = planner.plan_trip()

for i in range(len(itinerary)):
    if 'flying' in itinerary[i]:
        itinerary[i]['flying'] = f"Day {itinerary[i]['flying'].split('-')[0]}-{itinerary[i]['flying'].split('-')[1]}"

print(json.dumps(itinerary, indent=2))