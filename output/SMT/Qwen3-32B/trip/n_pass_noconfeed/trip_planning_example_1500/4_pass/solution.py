# Example of dynamic initialization from a dictionary
city_data = {
    0: 3,
    1: 5,
    2: 2,
    3: 4,
    4: 6,
    5: 1,
    6: 7,
    7: 3,
    8: 5,
    9: 2
}

required_days_by_index = [city_data[i] for i in range(10)]