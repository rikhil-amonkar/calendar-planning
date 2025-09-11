def is_valid(houses, stir_fry_house):
    # Ensure houses is a list
    if not isinstance(houses, list):
        return False
    
    # Ensure stir_fry_house is a valid integer index
    if not isinstance(stir_fry_house, int) or stir_fry_house < 0 or stir_fry_house >= len(houses):
        return False

    # Get the house data
    house_info = houses[stir_fry_house]

    # Ensure the house data is a sequence with at least 2 elements
    if not isinstance(house_info, (list, tuple)) or len(house_info) <= 1:
        return False

    # Now it's safe to access the second element
    return house_info[1] != 'Alice'