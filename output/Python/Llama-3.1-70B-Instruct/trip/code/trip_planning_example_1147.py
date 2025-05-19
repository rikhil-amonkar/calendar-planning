import json
from datetime import timedelta

class TripPlanner:
    def __init__(self, cities, constraints, direct_flights):
        self.cities = cities
        self.constraints = constraints
        self.direct_flights = direct_flights
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Attend an annual show in Istanbul between day 1 and day 5
        self.visit_city('Istanbul', 5)
        self.attend_event('Istanbul', 'annual show', 1, 5)

        # Visit Helsinki for 3 days
        self.fly_to('Helsinki', 'Istanbul')
        self.visit_city('Helsinki', 3)

        # Visit Brussels for 3 days
        self.fly_to('Brussels', 'Helsinki')
        self.visit_city('Brussels', 3)

        # Visit Milan for 4 days
        self.fly_to('Milan', 'Brussels')
        self.visit_city('Milan', 4)

        # Attend a wedding in Frankfurt between day 16 and day 18
        self.fly_to('Frankfurt', 'Milan')
        self.visit_city('Frankfurt', 3)
        self.attend_event('Frankfurt', 'wedding', 16, 18)

        # Attend a workshop in Vilnius between day 18 and day 22
        self.fly_to('Vilnius', 'Frankfurt')
        self.visit_city('Vilnius', 5)
        self.attend_event('Vilnius', 'workshop', 18, 22)

        # Visit other cities
        self.visit_other_cities()

        return self.itinerary

    def visit_city(self, city, days):
        self.itinerary.append({'day_range': f'Day {self.current_day}-{self.current_day + days - 1}', 'place': city})
        self.current_day += days

    def attend_event(self, city, event, start_day, end_day):
        self.itinerary.append({'day_range': f'Day {start_day}-{end_day}', f'{event}': city})

    def fly_to(self, to_city, from_city):
        self.itinerary.append({'flying': f'Day {self.current_day}-{self.current_day}', 'from': from_city, 'to': to_city})
        self.current_day += 1

    def visit_other_cities(self):
        cities_to_visit = ['Split', 'Dubrovnik']
        while cities_to_visit:
            for city in cities_to_visit:
                if city == 'Split':
                    self.fly_to('Split', self.itinerary[-1]['place'])
                    self.visit_city('Split', 4)
                    cities_to_visit.remove(city)
                elif city == 'Dubrovnik' and 'Split' in [x['place'] for x in self.itinerary]:
                    self.fly_to('Dubrovnik', self.itinerary[-1]['place'])
                    self.visit_city('Dubrovnik', 2)
                    cities_to_visit.remove(city)

def main():
    cities = ['Istanbul', 'Helsinki', 'Brussels', 'Milan', 'Frankfurt', 'Vilnius', 'Split', 'Dubrovnik']
    constraints = {
        'Istanbul': 5,
        'Helsinki': 3,
        'Brussels': 3,
        'Milan': 4,
        'Frankfurt': 3,
        'Vilnius': 5,
        'Split': 4,
        'Dubrovnik': 2
    }
    direct_flights = [
        ('Milan', 'Frankfurt'), ('Split', 'Frankfurt'), ('Milan', 'Split'), ('Brussels', 'Vilnius'), ('Brussels', 'Helsinki'), 
        ('Istanbul', 'Brussels'), ('Milan', 'Vilnius'), ('Brussels', 'Milan'), ('Istanbul', 'Helsinki'), ('Helsinki', 'Vilnius'), 
        ('Helsinki', 'Dubrovnik'), ('Split', 'Vilnius'), ('Dubrovnik', 'Istanbul'), ('Istanbul', 'Milan'), ('Helsinki', 'Frankfurt'), 
        ('Istanbul', 'Vilnius'), ('Split', 'Helsinki'), ('Milan', 'Helsinki'), ('Istanbul', 'Frankfurt'), ('Brussels', 'Frankfurt'), 
        ('Dubrovnik', 'Frankfurt'), ('Frankfurt', 'Vilnius')
    ]

    planner = TripPlanner(cities, constraints, direct_flights)
    itinerary = planner.plan_trip()
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()