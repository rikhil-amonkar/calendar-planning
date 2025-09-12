from enum import Enum

class City(Enum):
    Valencia = 'Valencia'
    Oslo = 'Oslo'
    Lyon = 'Lyon'
    Prague = 'Prague'
    Paris = 'Paris'
    Nice = 'Nice'
    Seville = 'Seville'
    Tallinn = 'Tallinn'
    Mykonos = 'Mykonos'
    Lisbon = 'Lisbon'

def get_duration(city_var):
    duration_map = {
        City.Valencia: 2,
        City.Oslo: 3,
        City.Lyon: 4,
        City.Prague: 3,
        City.Paris: 4,
        City.Nice: 4,
        City.Seville: 5,
        City.Tallinn: 2,
        City.Mykonos: 5,
        City.Lisbon: 2,
    }
    return duration_map.get(city_var, 0)