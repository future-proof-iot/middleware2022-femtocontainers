/*
 * Copyright (C) 2020 Koen Zandberg <koen@bergzand.net>
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @defgroup    boards_longan-nano Sipeed Longan Nano RISC-V board
 * @ingroup     boards
 * @brief       Support for the Sipeed Longan Nano RISC-V board
 * @{
 *
 * @file
 * @brief       Board specific definitions for the Sipeed Longan nano RISC-V
 *              board
 *
 * @author      Koen Zandberg <koen@bergzand.net>
 */

#ifndef BOARD_H
#define BOARD_H

#ifdef __cplusplus
extern "C" {
#endif

#include "macros/units.h"

/**
 * @name    Xtimer configuration
 * @{
 */
#define XTIMER_HZ                   MHZ(1)
#define XTIMER_WIDTH                (16)
/** @} */

/**
 * @brief   Initialize board specific hardware
 */
void board_init(void);

#ifdef __cplusplus
}
#endif

#endif /* BOARD_H */
/** @} */

