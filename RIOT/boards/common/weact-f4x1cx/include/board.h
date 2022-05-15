/*
 * Copyright (C) 2019 Benjamin Valentin
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     boards_common_weact-f4x1cx
 *
 * @brief       Support for the WeAct-F4x1Cx Board
 * @{
 *
 * @file
 * @brief       Pin definitions and board configuration options
 *
 * @author      Benjamin Valentin <benpicco@googlemail.com>
 */

#ifndef BOARD_H
#define BOARD_H

#ifdef __cplusplus
extern "C" {
#endif

#include "mtd.h"
#include "periph_cpu.h"

/**
 * @name    xtimer configuration
 * @{
 */
#define XTIMER_BACKOFF              (8)
#define XTIMER_OVERHEAD             (6)
/** @} */

/**
 * @name    LED pin definition and handlers
 * @{
 */
#define LED0_PORT           GPIOC
#define LED0_PIN            GPIO_PIN(PORT_C, 13)
#define LED0_MASK           (1 << 13)

#define LED0_ON             (LED0_PORT->BSRR = (LED0_MASK << 16))
#define LED0_OFF            (LED0_PORT->BSRR = (LED0_MASK <<  0))
#define LED0_TOGGLE         (LED0_PORT->ODR  ^= LED0_MASK)
/** @} */

/**
 * @name    User button pin definition
 * @{
 */
#define BTN0_PIN            GPIO_PIN(PORT_A, 0)
#define BTN0_MODE           GPIO_IN_PU
/** @} */

/**
 * @name WeAct-F4X1CX NOR flash hardware configuration
 *
 *       The pad for the NOR Flash (U3) is not populated.
 *       You have to solder a serial flash yourself and adjust the parameters.
 * @{
 */
#define WEACT_4X1CX_NOR_PAGE_SIZE          (256)
#define WEACT_4X1CX_NOR_PAGES_PER_SECTOR   (16)
#define WEACT_4X1CX_NOR_FLAGS              (SPI_NOR_F_SECT_4K | SPI_NOR_F_SECT_32K)
#define WEACT_4X1CX_NOR_SPI_DEV            SPI_DEV(0)
#define WEACT_4X1CX_NOR_SPI_CLK            SPI_CLK_10MHZ
#define WEACT_4X1CX_NOR_SPI_CS             GPIO_PIN(PORT_A, 4)
#define WEACT_4X1CX_NOR_SPI_MODE           SPI_MODE_0
/** @} */

/**
 * @name MTD configuration
 * @{
 */
extern mtd_dev_t *mtd0;
#define MTD_0 mtd0
/** @} */

#ifdef __cplusplus
}
#endif

#endif /* BOARD_H */
/** @} */
