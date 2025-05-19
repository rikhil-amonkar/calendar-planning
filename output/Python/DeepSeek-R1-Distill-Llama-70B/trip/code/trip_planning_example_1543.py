import json

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Prague': 3,
            'Warsaw': 4,
            'Dublin': 3,
            'Athens': 3,
            'Vilnius': 4,
            'Porto': 5,
            'London': 3,
            'Seville': 2,
            'Lisbon': 5,
            'Dubrovnik': 3
        }
        self.direct_flights = {
            'Warsaw': ['Vilnius', 'Athens', 'London', 'Porto', 'Prague', 'Dublin', 'Lisbon'],
            'Prague': ['Athens', 'Lisbon', 'London', 'Warsaw', 'Dublin'],
            'London': ['Lisbon', 'Dublin', 'Warsaw', 'Athens', 'Prague'],
            'Lisbon': ['Porto', 'Athens', 'Warsaw', 'Dublin', 'Seville'],
            'Porto': ['Warsaw', 'Dublin', 'Seville'],
            'Dublin': ['Seville', 'Porto', 'Athens', 'Warsaw'],
            'Athens': ['Vilnius', 'Dubrovnik', 'Warsaw', 'Porto', 'Prague', 'Lisbon'],
            'Vilnius': ['Warsaw', 'Athens'],
            'Seville': ['Porto', 'Lisbon'],
            'Dubrovnik': ['Athens']
        }
        self.itinerary = []
        self.current_day = 1

    def plan_trip(self):
        # Start with Prague for the workshop
        self.add_place('Prague', 3)
        # Fly to London for the wedding
        self.add_flight('Prague', 'London')
        self.add_place('London', 3)
        # Fly to Lisbon to visit relatives
        self.add_flight('London', 'Lisbon')
        self.add_place('Lisbon', 5)
        # Fly to Porto for the conference
        self.add_flight('Lisbon', 'Porto')
        self.add_place('Porto', 5)
        # Fly to Dublin
        self.add_flight('Porto', 'Dublin')
        self.add_place('Dublin', 3)
        # Fly to Seville
        self.add_flight('Dublin', 'Seville')
        self.add_place('Seville', 2)
        # Fly to Athens
        self.add_flight('Seville', 'Athens')
        self.add_place('Athens', 3)
        # Fly to Dubrovnik
        self.add_flight('Athens', 'Dubrovnik')
        self.add_place('Dubrovnik', 3)
        # Fly to Vilnius
        self.add_flight('Dubrovnik', 'Vilnius')
        self.add_place('Vilnius', 4)
        # Fly to Warsaw to meet friends
        self.add_flight('Vilnius', 'Warsaw')
        self.add_place('Warsaw', 4)

    def add_place(self, place, days):
        end_day = self.current_day + days - 1
        self.itinerary.append({'day_range': f'Day {self.current_day}-{end_day}', 'place': place})
        self.current_day = end_day + 1

    def add_flight(self, from_city, to_city):
        self.itinerary.append({'flying': f'Day {self.current_day}-{self.current_day}', 'from': from_city, 'to': to_city})
        self.current_day += 1

planner = TripPlanner()
planner.plan_trip()
print(json.dumps(planner.itinerary))